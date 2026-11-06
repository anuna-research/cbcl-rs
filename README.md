<img src="https://imagedelivery.net/O-SJhBv1S1zUZFvTxrBOhQ/0ab77afb-28f0-44cd-4c8f-ddc2522ca500/smalllogo" alt="CBCL logo" width="350">

# CBCL

**A language for composing multi-agent protocols.**

CBCL (Common Business Communication Language) lets agents define, exchange, and participate in multiparty protocols at runtime, without a central coordinator or a shared global message order. This repository provides the Rust implementation and Lean proofs.

Agents teach each other new interaction vocabularies as messages. Protocols can also define shared state and bounded resources: replicas derive state from accepted acts, while escrow rights constrain concurrent spending. Signed, content-addressed evidence supports verification of public protocol behaviour and detection of equivocation.

These guarantees concern observable interactions. They do not establish that an agent’s claims are true or that compliant actions are beneficial.

## Quick start

Install Rust stable, then:

```bash
git clone https://git.anuna.io/anuna-research/cbcl-rs
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

## Message store

Each agent keeps a local, content-addressed message store. Messages belong to threads and cite predecessor content addresses through `:caused-by`. Each message’s address commits to those references. With authenticated content addresses and admission requiring already-accepted predecessors, accepted history forms a causal Merkle DAG; the raw store alone does not enforce these conditions. The store is an append-only, deduplicated set: exchanging messages merges knowledge by set union, without requiring a global delivery order. The core provides an in-memory implementation; transport and durable storage belong to the host.

Verification consults this store for predecessor evidence. If a required predecessor has not arrived, the result can remain `Unknown`; later delivery lets the agent check again. Causal-closure bundles package a message and its transitive predecessors for transfer, while the frontier identifies messages not yet referenced by another message in the thread.

Receipt alone does not mean acceptance. The admission monitor separates pending candidates from accepted history and verifies against accepted predecessors. State rules then derive an object's state from its accepted acts. Replicas with different evidence can temporarily differ; replicas with the same accepted acts derive the same state.

## State and bounded counters

An optional `(state …)` declaration gives a protocol's messages a shared state interpretation. Registers, sets, maps, and counters are derived from the accepted acts in a thread. The same accepted set produces the same state regardless of arrival order or duplicate delivery. `fold` computes that state; `intend` binds a proposed act against it. These primitives are exposed through the Rust, JavaScript/TypeScript, WASM, C, and Erlang interfaces.

The **bounded-counter primitive** represents transferable rights over constrained resources, supporting balances, quotas, credits, and inventory. These escrow rights are bound to authenticated accounts: each account can decrement within its allocation, and transferring rights changes who can spend without changing the total. An optional ceiling adds per-account headroom for increments. Concurrent operations are authorized against these allocations rather than a global observed balance.

| Operation | Effect |
|-----------|--------|
| Increment | Raises the value; requires issuer authority and, when capped, headroom |
| Decrement | Lowers the value; consumes the signer's rights |
| Transfer | Moves rights between accounts; preserves the value |

Account ownership and collective ownership support individual allocations and pools consumed by distinct authorized signers. Examples: `dialects/example-coin.cbcl`, `dialects/example-capped-coin.cbcl`, and `dialects/example-collective-tickets.cbcl`. See [bounded-counter guide](docs/concepts/bounded-counter.md) for declarations and invariants.

The default certification profile requires a durable host issuance gate. `(certification quorum-budget)` selects the Rust validator runtime with authenticated quorums, multi-parent DAG adoption, durable journals, and cancellation-backed refunds. Signing, authentication, persistence, and external-effect deduplication remain host responsibilities. Quorum balance queries report known-final local views, with completeness unknown. See [quorum runtime API](docs/reference/quorum-runtime.md).

## Architecture

`cbcl-core` and `cbcl-parser` form the deterministic `no_std + alloc` core and forbid unsafe code. CLI, WASM, C FFI, and Erlang NIF crates provide the effectful interfaces.

Lean proofs live in `lean-cbcl/`, including R1–R5 properties, endpoint-projection correspondence, finite-time delivery results, and R6 DCFL preservation. Splicing and selective-disclosure results concern abstract predecessor-type evidence; concrete field-opening authentication remains a separate refinement obligation. Explicit host-HLC LWW registers and conflict-preserving aliases are described in [HLC registers](docs/concepts/hlc-registers.md); their clock honesty premise is separate from resource certification. State-fold and binder properties are proved in `State.lean`; corpus tests check Rust/model correspondence, while universal Rust-driver refinement remains open. The concrete R6 checks are tested in Rust; their semantic guarantees are mechanised in Lean. The axiom audit allowlist includes explicit content-hash and causal-accessor assumptions. For proof boundaries, see [proof design notes](proofs/epp-correspondence/design.md) and `scripts/check-axioms.sh`.

## API reference

Generate local Rust documentation with `cargo doc --workspace --no-deps`. Start with:

| Task | API |
|------|-----|
| Parse and validate | `cbcl_parser::run_pipeline` |
| Store messages and traverse causality | `cbcl_core::store::{MessageStore, ThreadedMessageStore, CausalClosureBundle}` |
| Admit messages into accepted history | `cbcl_core::admission::AdmissionMonitor` |
| Verify causal evidence | `cbcl_core::protocol::verify_causal` |
| Compute state and bind intent | `cbcl_core::state::fold`, `cbcl_core::intend::intend` |
| Project and verify roles | `cbcl_core::projection::{project, verify_causal_for_role}` |
| Open committed fields | `cbcl_core::typed_addr::{typed_root, open, verify_opening}` |
| Authenticate disclosed evidence | `cbcl_core::envelope::{build_opened, verify_opened}` |

## Development

```bash
make check
cargo bench --workspace
```

Run `make help` for build, install, distribution, and documentation targets. `make install` installs the CLI as `cbcl` under `~/.local/bin` (override `PREFIX` as needed). `make dist` stages a native binary and checksum locally.

To release from a clean `main` matching `origin/main`, run `./release.sh X.Y.Z` with a higher stable version. It updates the shared workspace version and lockfile, runs Rust and Lean checks, commits, and pushes `main` plus an annotated `vX.Y.Z` tag atomically. It does not publish packages or binaries. Git, Rust, Make, Python 3, and Lean/lake are required.

For proof changes, install Lean via elan and run `lake build` and `lake exe runLinter LeanCbcl` from `lean-cbcl/`. Run `scripts/check-axioms.sh` from the repository root. For mutation testing, see [mutation-testing guide](docs/mutation-testing.md).

Contributions are welcome. Specs live under `specs/`, implementation plans under `plans/`, and bug reports under `bugs/`. Link changes to their governing requirements and verification evidence.

State conformance vectors live in `test-vectors/state/`. For client-observed certificate finality measurements, see [quorum benchmark](tools/quorum-e2e/README.md).

## Background and license

The theoretical framework is published in the [2026 IEEE Symposium on Security and Privacy Workshops (SPW)](https://www.computer.org/csdl/proceedings-article/spw/2026/107000a039/2hIfzFiEfjG), pp. 39–48. A [preprint](https://arxiv.org/abs/2604.14512) is also available. The original prototype is the [Scheme implementation](https://github.com/anuna-research/cbcl).

Apache-2.0; see LICENSE.

## Citation

```bibtex
@inproceedings{cbcl2026,
  title     = {{CBCL}: Safe Self-Extending Agent Communication},
  author    = {O'Connor, Hugo},
  booktitle = {2026 IEEE Symposium on Security and Privacy Workshops (SPW)},
  year      = {2026},
  pages     = {39--48},
  publisher = {IEEE},
  doi       = {10.1109/SPW72489.2026.00007},
  url       = {https://www.computer.org/csdl/proceedings-article/spw/2026/107000a039/2hIfzFiEfjG}
}
```
