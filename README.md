<img src="https://imagedelivery.net/O-SJhBv1S1zUZFvTxrBOhQ/0ab77afb-28f0-44cd-4c8f-ddc2522ca500/smalllogo" alt="CBCL logo" width="350">

# CBCL

**A language for composing multi-agent protocols.**

CBCL (Common Business Communication Language) lets agents define, exchange, and participate in multiparty protocols at runtime, without a central coordinator or a shared global message order. This repository provides the Rust implementation and Lean proofs.

Agents teach each other new interaction vocabularies as messages. Protocols can also define shared state and bounded resources: replicas derive state from accepted acts, while escrow rights constrain concurrent spending. Signed, content-addressed evidence supports verification of public protocol behaviour and detection of equivocation.

These guarantees concern observable interactions. They do not establish that an agent’s claims are true or that compliant actions are beneficial.

## How it works

CBCL defines interaction protocols over sets of recorded speech acts. Each participant holds a set of signed, content-addressed acts; sets merge by union, acts cite the acts they respond to, and a dialect says which citations are valid. The flow below follows one act from receipt to derived state.

```text
   incoming messages, any bytes
                 |
                 v
 (0) full recognition: is it in L_E?
     L_E = the language the installed
           environment E recognises
        |      \
        | yes   no -> rejected
        v
   Alice {p, a}       Bob {p, c}
          \             /
           +-----------+
                 |  set union
                 v
 (1) S = {p, a, c}  received records
                 |
                 v
 (2) proposal -> approval -> completion
     arrow reads "cited as evidence by"
                 |
                 v
 (3) check against dialect D
     +----------------------------+
     | Types   what act is this?  |
     | Roles   who may perform it?|
     | Causes  what must it cite? |
     +----------------------------+
        |          |          |
     Unknown     Valid     Violation
     evidence    check     breach
     missing;    passes    established
     wait and
     recheck
                 |
                 v
 (4) A, the accepted subset of S
                 |
                 v
 (5) State = f_D(A)
     approvals, balances, progress
```

0. **Full recognition.** The installed environment E fixes an input language L_E, a deterministic context-free language. Every incoming message is recognised in full against it before any semantic action: the whole input is consumed and parsed, anything outside L_E is rejected, and only recognised messages become records. Installing a dialect extends L_E without losing this property.
1. **Union.** Duplicates change nothing, and no global arrival order is required.
2. **Citations.** Dependencies come from what an act cites, not from the order records arrive.
3. **Check.** Each candidate is checked under the dialect in scope. `Unknown` returns to this step when more evidence arrives.
4. **Admission.** Acceptance requires authenticated acts and accepted predecessors. Passing one causal check alone does not admit an act.
5. **State.** The same accepted acts under the same fixed rules give the same derived state.

The same model written as a theorem over sets and functions, with the Lean declaration behind each claim, is in [protocol model](docs/concepts/protocol-model.md).

Verdicts in step (3) follow strong Kleene three-valued logic, ordered `Violation < Unknown < Valid`: a conjunction of checks takes the least verdict and a disjunction the greatest, so `Unknown` is kept until evidence resolves it.

Three concerns sit beside the main flow:

- **Runtime self-extension.** A dialect is communicated as records, verified, installed, and then used in an explicit `(lang …)` scope. The installed dialect supplies the rules step (3) applies. New dialects do not silently rewrite the meaning of old acts.
- **Separate responsibilities.** Transport delivers records; cryptography authenticates authors and integrity; CBCL defines and verifies interaction rules. These are responsibilities, not necessarily sequential processing stages.
- **Bounded resources.** Rights plus issuance or certification discipline constrain spending. Set union alone does not prevent double spending.

Recorded speech acts become evidence for subsequent interactions. Authentication establishes who said what, not that the statement is true. A larger version of this diagram is in [docs/diagrams/cbcl-architecture.svg](docs/diagrams/cbcl-architecture.svg).

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

The state layer interprets the accepted interactions of the multiparty protocol;
protocol and role checks govern admission, while state rules govern observations.
An HLC orders eligible state writes, not protocol execution. State fields choose
different concurrency policies: `initial` reads immutable
opener data; multi-value registers/maps preserve concurrent surviving values;
explicit `lww-*` registers choose a winner using trusted-host HLC evidence; and
sets, events and aggregates combine evidence according to their rules. Explicit
supersession and timestamp arbitration are separate: `lww-map` removes replaced
writes before choosing a survivor, and deletion leaves unobserved concurrent
writes intact. Bounded counters add separate resource authorization. See
[[hlc-registers#Choosing a state rule|choosing a state rule]] for examples and assumptions.

The **bounded-counter primitive** represents transferable rights over constrained resources, supporting balances, quotas, credits, and inventory. These escrow rights are bound to authenticated accounts: each account can decrement within its allocation, and transferring rights changes who can spend without changing the total. An optional ceiling adds per-account headroom for increments. Concurrent operations are authorized against these allocations rather than a global observed balance.

| Operation | Effect |
|-----------|--------|
| Increment | Raises the value; requires issuer authority and, when capped, headroom |
| Decrement | Lowers the value; consumes the signer's rights |
| Transfer | Moves rights between accounts; preserves the value |

Account ownership and collective ownership support individual allocations and pools consumed by distinct authorized signers. Examples: `dialects/example-coin.cbcl`, `dialects/example-capped-coin.cbcl`, and `dialects/example-collective-tickets.cbcl`. See [bounded-counter guide](docs/concepts/bounded-counter.md) for declarations and invariants.

The built-in checkpoint companion dialect supports cached member-certified state
opening through `cbcl-checkpoint`. It reuses native signed endorsements, verifies
continuation and local-history coverage, and retains signed evidence. It supplies
neither resource-release authority nor global freshness. See
[checkpoint runtime](crates/cbcl-checkpoint/README.md).

### Example: a coin with a bounded counter

`dialects/example-coin.cbcl` declares a coin. `open` fixes each account's allocation, `mint` and `burn` change the value, and `pay` moves spending rights between accounts without changing the value:

```lisp
; Bounded-counter example. Amounts are integer base units, not decimals.
; Hosts authenticate acts and serialize issuance per account before publication.
(define example-coin (cbcl) @coin-author
  (:resource-requirements ((max-depth 16) (max-expansion-size 4096) (verification-time 1000)))
  (:roles (issuer (* holder)))
  (extend open (to name allocations) :from issuer :to (issuer holder)
    (tell to :name name :allocations allocations))
  (extend mint (to amount) :from issuer :to (issuer holder)
    (tell to :amount amount))
  (extend burn (to amount) :from holder :to (issuer holder)
    (tell to :amount amount))
  (extend pay (to recipient amount) :from holder :to (issuer holder)
    (tell to :recipient recipient :amount amount))
  (shape open (require :name string) (require :allocations list))
  (shape mint (require :amount number))
  (shape burn (require :amount number))
  (shape pay (require :recipient symbol) (require :amount number))
  (protocol (then begin open) (then open mint) (then open burn) (then open pay))
  (state
    (name (initial open :name))
    (coins (bounded-counter
      (floor 0)
      (initial-rights open :allocations)
      (issuers issuer)
      (increment mint :amount)
      (decrement burn :amount)
      (transfer pay :recipient :amount)))))
```

The `issuer` role may mint; any `holder` may burn or pay. The source account of every operation is the authenticated signer, never a caller-supplied field. Verify the dialect with:

```bash
cargo run -p cbcl-cli -- verify < dialects/example-coin.cbcl
```

#### Sending messages in the dialect

A thread starts with a root act that fixes the cast, binding each role to agent keys:

```lisp
(with-roles ((issuer @treasury) (holder @treasury @alice @bob))
  (signed @treasury
    (hello () :thread "coin-1" :caused-by begin)))
```

Every later act names the dialect with `(lang example-coin …)`. A performative takes the recipient list, a content slot (empty here), the keyword fields its `shape` requires, and the routing fields `:from`, `:thread` and `:caused-by`. The opening act cites the root's content address:

```lisp
(signed @treasury
  (lang example-coin
    (open (@alice @bob @treasury) ()
      :name "Example Coin"
      :allocations ((@treasury 1000) (@alice 0) (@bob 0))
      :from @treasury
      :thread "coin-1"
      :caused-by sha256-6655c6fbcd385dd84414cad93d6cad9a1ed650f4c2834790d9043f543051d407)))
```

A payment cites the opening act. The binder adds `:escrow-prev` and `:escrow-deps`, which record resource causality separately from the protocol's `:caused-by`:

```lisp
(signed @treasury
  (lang example-coin
    (pay (@alice @bob @treasury) ()
      :recipient @alice
      :amount 100
      :escrow-prev sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5
      :escrow-deps ()
      :from @treasury
      :thread "coin-1"
      :caused-by sha256-a9d6de157c34d0473ad88f651a6701c40415978732593f22bf77b4fb0a448ca5)))
```

Hosts do not write these by hand. `intend` completes a verb and its business fields into the canonical act above, ready for the host to sign and publish:

```rust
let inst = Instance::new(&dialect, ThreadId("coin-1".into()), &accepted_acts)?;
let fields = BTreeMap::from([
    ("recipient".to_string(), SExpr::Atom(Atom::Symbol("@alice".into()))),
    ("amount".to_string(), SExpr::Atom(Atom::Num(100))),
]);
let act = intend(&inst, &AgentKey("@treasury".into()), "pay", fields)?;
```

The `signed` wrapper names the signer; the host's authentication, not the wrapper, establishes it. The complete message sequence for this example is in `test-vectors/state/bounded-coin.json`.

#### How identities, roles and allocations connect

`@treasury` is a key identity, short for `@ed25519:treasury`. The core never holds public keys: the host maps each identity to real key material, verifies the signature over the act's header, and only then passes the signer to the core. The root act's `with-roles` cast binds identities to roles and is immutable for the thread. The opener's `:allocations` binds the same identities to rights; every account must be in the cast, and each operation debits the authenticated signer. One host-side signature check therefore anchors role, account and rights.

The trace from `crates/cbcl-parser/tests/bounded_counter.rs` opens the coin with allocations `((@treasury 1000) (@alice 0) (@bob 0))` and then applies four acts:

| Act | Signer | Rights afterwards | Value |
|-----|--------|-------------------|-------|
| `pay :recipient @alice :amount 100` | `@treasury` | treasury 900, alice 100 | 1000 |
| `pay :recipient @bob :amount 25` | `@alice` | alice 75, bob 25 | 1000 |
| `burn :amount 5` | `@bob` | bob 20 | 995 |
| `mint :amount 250` | `@treasury` | treasury 1150 | 1245 |

`fold` over the accepted acts renders the state as:

```json
{"name":"Example Coin","coins":{"status":"ready","value":1245,"rights":{"@treasury":1150,"@alice":75,"@bob":20}}}
```

A `pay` or `burn` that exceeds the signer's rights is refused with the reason `insufficient rights`, even when another account has unused rights; the signer needs a transfer first. When a cited resource predecessor has not arrived, the field reports `pending` rather than a partial balance. Replicas that merge the same acts in different orders derive the same rights table.

The default certification profile requires a durable host issuance gate. `(certification quorum-budget)` selects the Rust validator runtime with authenticated quorums, multi-parent DAG adoption, durable journals, and cancellation-backed refunds. Signing, authentication, persistence, and external-effect deduplication remain host responsibilities. Quorum balance queries report known-final local views, with completeness unknown. See [quorum runtime API](docs/reference/quorum-runtime.md).

## Architecture

`cbcl-core` and `cbcl-parser` form the deterministic `no_std + alloc` core and forbid unsafe code. CLI, WASM, C FFI, and Erlang NIF crates provide the effectful interfaces.

Lean proofs live in `lean-cbcl/`, including R1–R5 properties, endpoint-projection correspondence, finite-time delivery results, and R6 DCFL preservation. Splicing and selective-disclosure results concern abstract predecessor-type evidence; concrete field-opening authentication remains a separate refinement obligation. Explicit host-HLC LWW registers and conflict-preserving aliases are described in [HLC registers](docs/concepts/hlc-registers.md); their clock honesty premise is separate from resource certification. State-fold and binder properties are proved in `State.lean`; [conditional strong eventual consistency](specs/SPEC-037-state-kernel-sec.md) connects equal-set observations to fair admission and eventual delivery; [whole typed kernel correctness](specs/SPEC-036-state-kernel-correctness.md) additionally proves independent denotational correctness and elaboration completeness for arbitrary finite supported clauses, with resource-verifier classification explicitly outside the theorem; corpus tests check Rust/model correspondence, while universal Rust-driver refinement remains open. The concrete R6 checks are tested in Rust; their semantic guarantees are mechanised in Lean. The axiom audit allowlist includes explicit content-hash and causal-accessor assumptions. For proof boundaries, see [proof design notes](proofs/epp-correspondence/design.md) and `scripts/check-axioms.sh`.

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

Cached-checkpoint continuation for all 16 native rule heads is proved in
[`CheckpointAll.lean`](lean-cbcl/LeanCbcl/CheckpointAll.lean), including ordered
aggregate sources and projected protocol/resource facts. The theorem connects
compact incremental state to the existing native evaluator over accepted
identities; it is not a universal Rust extraction or resource-finality proof.
See the [proof guide](lean-cbcl/README.md#cached-checkpoint-continuation) for the boundary
and reproducible checks.

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
