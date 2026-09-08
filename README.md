<img src="https://imagedelivery.net/O-SJhBv1S1zUZFvTxrBOhQ/0ab77afb-28f0-44cd-4c8f-ddc2522ca500/smalllogo" alt="CBCL logo" width="350">

# CBCL

[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![Rust: 1.75+](https://img.shields.io/badge/rust-1.75%2B-orange.svg)](rust-toolchain.toml)
[![Lean 4](https://img.shields.io/badge/lean-4-purple.svg)](lean-cbcl/)
[![Sorries: 0](https://img.shields.io/badge/sorries-0-brightgreen.svg)](lean-cbcl/)
[![no_std](https://img.shields.io/badge/no__std-%2B%20alloc-lightgrey.svg)](#architecture)
[![WASM](https://img.shields.io/badge/wasm32-unknown--unknown-654FF0.svg)](crates/cbcl-wasm)
[![LangSec '26](https://img.shields.io/badge/LangSec-'26-8a2be2.svg)](https://arxiv.org/abs/2604.14512)
[![arXiv](https://img.shields.io/badge/arXiv-2604.14512-b31b1b.svg)](https://arxiv.org/abs/2604.14512)

Rust implementation of **CBCL** (Common Business Communication Language): a safely extensible agent communication language with formal guarantees. CBCL restricts agent messages to the deterministic context-free (DCFL) language class, so message validity stays decidable as agents define new dialects at runtime. Safety under extension rests on six invariants: three structural (R1–R3), one cryptographic (R4), one for optional message contracts (R5), and one for the opt-in multiparty role layer (R6), all enforced by the same parser that handles ordinary communication.

## Quick start

Prerequisites: Rust 1.75+ (the workspace toolchain is pinned in `rust-toolchain.toml`). For the Lean proofs, install Lean 4 via [elan](https://github.com/leanprover/elan).

```bash
git clone https://codeberg.org/anuna/cbcl-rs
cd cbcl-rs

# Run tests (1356 passing tests across 32 suites; 19 ignored)
cargo test --workspace

# Parse a message
cargo run -p cbcl-cli -- parse '(tell agent-b "hello")'

# Verify a dialect (R1, R2, R3, R5)
cargo run -p cbcl-cli -- verify dialect.scm

# Run benchmarks
cargo bench --workspace

# Build for WASM
cargo build --target wasm32-unknown-unknown -p cbcl-wasm
```

For the Lean 4 proofs:

```bash
cd lean-cbcl && lake build
```

## The problem

Language-theoretic security (LangSec) teaches that the computational complexity class of an input language determines the *category* of bugs its parsers can exhibit. Regular languages admit only finite-state bugs; context-free languages add stack-related bugs; Turing-complete inputs make parser correctness undecidable.

Agent communication protocols have moved *up* this hierarchy without acknowledging the security consequences:

| Protocol | Input Complexity | Extensible? | Verifiable? | Weird Machines? |
|----------|-----------------|-------------|-------------|-----------------|
| KQML | CFG | No | Partially | Stack-based |
| FIPA-ACL | CFG | No | Partially | Stack-based |
| MCP | Unrestricted JSON | Yes | No | Turing-complete |
| LLM Agents | Natural language | Yes | No | Turing-complete |
| **CBCL** | **DCFL** | **Yes** | **Yes** | **None (by construction)** |

Early ACLs (KQML, FIPA-ACL) had fixed vocabularies that couldn't evolve without out-of-band standardisation. The modern alternative, natural language and unrestricted JSON (MCP, LLM agent frameworks), provides unlimited extensibility but creates an input language whose computational complexity is effectively unbounded. Determining whether an arbitrary message will cause harmful behaviour requires solving undecidable problems.

## The solution

CBCL sits between these extremes: a small core vocabulary (8 performatives) with a formal mechanism for agents to define, exchange, and adopt new domain-specific vocabularies ("dialects") at runtime, without centralised coordination and without escaping the DCFL complexity class.

The key insight is *homoiconic self-extension*: dialect definitions are themselves valid CBCL messages in S-expression syntax, parsed and verified by the same deterministic pushdown automaton used for ordinary communication. Safety constraints, verified in Lean 4 and enforced at runtime, ensure this self-extension is provably safe:

- **R1 (No Recursion):** Dialect templates are purely declarative pattern-template substitutions. No cyclic dependencies, iteration, or reflection.
- **R2 (Resource Bounds):** Every dialect declares static resource limits (depth, expansion size, verification time) enforced at both definition time and runtime.
- **R3 (Core Preservation):** The eight core performatives (`tell`, `ask`, `reply`, `hello`, `bye`, `ok`, `error`, `cancel`) cannot be redefined by any dialect.
- **R4 (Integrity):** Dialects carry an Ed25519-style signature over their canonical byte encoding (`Signer` trait); install accepts `Valid` and `Unsigned` (with warning) and rejects `Invalid`, so a dialect's authorship and bit-exact contents can be checked before any further safety constraint runs.
- **R5 (Contract Well-formedness):** Optional `(protocol …)` and `(shape …)` clauses on a dialect (its causal-message contract and per-performative shape contracts) must be acyclic, fully reachable from `begin`, reference only defined performatives (with ancestor closure for `extends`), have no duplicate steps, and respect the dialect's R2 depth bound. All five sub-checks run at install time and terminate in time linear in the dialect's size.
- **R6 (Multiparty Well-formedness):** When a dialect's protocol carries `:roles`/`:from`/`:to` annotations, it must be role-complete, chooser-coherent, projectable onto every role, *causally local* (every endpoint role of a performative is an endpoint of each predecessor type its `:caused-by` clause names), reachable for every role, and single-decider at every choice. Checked at install time in O(|P|² · |R|) table lookups; causal locality is what makes coordination-free role-local verification agree with a whole-conversation verifier (the endpoint-projection correspondence, mechanised in `lean-cbcl` — see [Formal verification](#formal-verification)). Role annotations stay inside the DCFL class, machine-checked at both levels: the syntax inhabits the existing S-expression grammar, and protocol trace languages are regular with projection adding no recogniser (`R6DCFLPreservation.lean`).

**Why DCFL?** It is the minimal complexity class that supports nested structure (agent messages have envelopes wrapping messages, dialects scoping inner messages) while guaranteeing *parser equivalence*: every conformant implementation produces exactly one parse tree for every input. This eliminates parser differential attacks by construction. Regular languages are insufficient for nesting; general CFG introduces ambiguity; anything above DCFL makes validity checking undecidable.

Named after McCarthy's 1982 proposal for a "Common Business Communication Language" that would be "open ended so that as programs improve, programs that can at first only order by stock numbers can later be programmed to inquire about specifications and prices."

Full theoretical framework and proofs are in the LangSec '26 paper, available as a preprint: [arXiv:2604.14512](https://arxiv.org/abs/2604.14512). The original prototype is the [Scheme implementation](https://github.com/anuna-research/cbcl).

## Features

- **Linear-time parser.** S-expression parser with O(n) time complexity and fuel-bounded recursion.
- **Full message grammar.** Core performatives, dialects, and templates, all parsed by one DPDA.
- **Verified safety constraints.** R1 (no recursion), R2 (resource bounds), R3 (core preservation), R4 (integrity), R5 (causal-protocol + shape contract well-formedness), each machine-checked in Lean 4.
- **Multiparty roles (R6).** Opt-in role layer over R5: `:roles`/`:from`/`:to` annotations, installation-time R6 checks, coordination-free endpoint projection, and role-local verification composed with the R5 verifier — no central compiler or ordered transport. Projection and gluing satisfy a machine-checked run-level correspondence (`epp_correspondence`), a temporal bridge to conformant executions (`temporal_bridge`), and a splicing analysis pinning causal locality as the condition role-local checking needs (`weakest_sound_condition`); typed content addresses (`typed_addr`, Merkle-over-fields) give field-openings for selective disclosure (`openings_suffice`) ([SPEC-014](specs/SPEC-014-role-layer-endpoint-projection.md); modules `role`, `r6`, `projection`, `splice`, `typed_addr`, `envelope`, `attest`, `equivocation`; correspondence theorems mechanised in `lean-cbcl`).
- **Deterministic message tagging** preserving DCFL properties under dialect union.
- **Embedded-friendly.** `no_std + alloc` compatible pure core; `#![forbid(unsafe_code)]`.
- **Polyglot bindings.** WASM target (`wasm32-unknown-unknown`) via `wasm-bindgen`; C FFI via `cbindgen`; Erlang/BEAM NIF via `rustler`.
- **CLI tooling.** Parsing, verification, agent REPL, gossip simulation.

## Workspace

| Crate | Zone | Description |
|-------|------|-------------|
| `cbcl-core` | Pure | Types, constraints (R1–R6), role layer + endpoint projection, template expansion, gossip, evaluator |
| `cbcl-parser` | Pure | S-expression and message parser, pipeline |
| `cbcl-cli` | Shell | Command-line interface |
| `cbcl-wasm` | Shell | WebAssembly bindings |
| `cbcl-ffi` | Shell | C FFI bindings |
| `cbcl-erl` | Shell | Erlang/BEAM NIF bindings via `rustler` |
| `lean-cbcl` | Proofs | Lean 4 formal verification of core algorithms |

## Related projects

- [`cbcl-router`](https://codeberg.org/anuna/cbcl-router) — BEAM/LFE router
  that uses this crate's parser and R1–R4 validators on every message,
  dispatching asks from authenticated producers to capability-registered
  agents.
- [`hark`](https://codeberg.org/anuna/hark) — Rust CLI and per-user daemon
  that connects an agent to `cbcl-router`, linking this crate for local parse
  and R1–R5 validation at the `/send` and `recv` boundaries.

## Formal verification

The `lean-cbcl/` directory contains a Lean 4 formalisation that machine-checks the core safety properties. Zero sorries, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`). R1–R5 checkers are verified directly against their contracts; for R6 the mechanisation covers the *semantic* guarantees the checks purchase — the endpoint-projection correspondence, projectability ≡ local verifiability, the splicing/type-opacity analysis, the temporal bridge, and DCFL preservation (role syntax adds no grammar; protocol trace languages are regular, and projection adds no recogniser) — while the R6 table checks themselves are exercised by property tests mirroring the Lean model ([SPEC-014](specs/SPEC-014-role-layer-endpoint-projection.md)).

| Rust module | Lean file | What is proved |
|---|---|---|
| `sexpr.rs` | `SExpr.lean` | S-expression type well-formedness, `DecidableEq` |
| `parser.rs` | `Parser.lean` | Parser soundness (`WellFormedSExpr`), concrete parse tests |
| `serializer.rs` | `Serializer.lean` | Round-trip theorem for `SafeSymbol`, `RoundTrippable'` spec |
| `msg.rs` | `MessageParser.lean` | Grammar soundness + completeness (`ValidMessageGrammar` ↔ `parseMessage`) |
| `r1.rs` | `R1NoRecursion.lean` | DFS cycle detection: **sound** (`true → ¬cycle`) **and complete** (`cycle → false`) |
| `r2.rs` | `R2ResourceBounds.lean` | Bounded evaluation terminates; depth returns to original level |
| `r3.rs` | `R3CorePreservation.lean` | Core performatives cannot be redefined by extension dialects |
| `r5.rs`, `protocol.rs` | `R5.lean` | Causal-protocol + shape contract well-formedness: acyclicity, reachability, performative definedness, step uniqueness, with full iff theorems for all four sub-checks |
| `protocol.rs` (verify_causal) | `Verify.lean`, `Lattice/Result.lean`, `Lattice/Store.lean` | `verify : Message × CausalProtocol × MessageStore → VerificationResult` is monotone in the store, `(all …)` fan-in is the eager meet, and replica results join coordination-free under store union (G-Set merge). The store is a genuine lattice; the verdict is not — see `Lattice/NotALattice.lean` |
| `role.rs`, `r6.rs`, `projection.rs` | `EPP.lean`, `EPPCompletion.lean`, `ProtocolProjection.lean` | Endpoint-projection correspondence (run-level): `project`/`glue` are mutually inverse on closed configurations (both round trips), and role-local verification is sound and complete for whole-conversation safety (`epp_correspondence`, `epp_correspondence_complete`). The protocol-side projection (`projection.rs`'s bystander erasure/splice) enters through an agreement interface: any projected protocol agreeing with `P` on r-endpoint performatives assigns identical verdicts (`AgreesOnRole`, `local_protocol_verification_agrees`); that the concrete splice satisfies the interface under causal locality is the paper-level step |
| `splice.rs`, `typed_addr.rs` | `Splice.lean` | Splicing analysis + typed content addresses: a spliced (non-local) predecessor stays permanently `Unknown`; role-local verification decides a closed configuration iff every cited predecessor is role-local (`decidesAll ↔ predsLocal`); a typed field-opening carries exactly the predecessor type the verdict reads (`spliced_pred_permanently_unknown`, `weakest_sound_condition`, `openings_suffice`) |
| `protocol.rs` (verify_causal) | `Bridge.lean` | Conformant executions — monotone delivery schedules accumulating a closed configuration — embed into the correspondence (`temporal_bridge`) |
| `role.rs`, `projection.rs`, `protocol.rs` (verify_causal) | `R6DCFLPreservation.lean` | DCFL preservation at R6. Syntax half (typechecking-level): the role-annotation surface forms inhabit the existing S-expression grammar. Trace half, with `verify_causal`'s clause semantics (disjunctive `Single`/`Any` pool, first-`(all …)` fan-in, undeclared performatives unconstrained): both the causal-order trace language (`causalTrace_regular`) and the deployed order-free acceptance — valid-sticky verdicts, every message eventually `Valid` (`storeTrace_regular`) — are regular, hence trace-DCFL, with `causalTrace_storeTrace` embedding the former in the latter and the projected protocol recognised by the same builder |
| `protocol.rs` (verdict) | `Lattice/NotALattice.lean` | The three-valued verdict is a bounded meet-semilattice under the knowledge order (GLB is the consensus meet, `Valid ⊓ Violation = Unknown`) and a bisemilattice for the deployed eager operators (absorption fails) — provably **not** a lattice (`not_a_lattice`, `no_join_of_terminals`, `kmeet_is_glb`, `eager_absorption_fails`) |
| `dialect.rs` (`base_definer_of`), `evaluator.rs` | `Agent.lean` | Custom names require a lang scope (`resolvePerformative_unscoped_custom`); scoped resolution is independent of other installed dialects (`resolvePerformative_scoped_custom`) and has no fallback (`resolvePerformative_no_fallback`) |
| `template.rs` | `TemplateExpansion.lean` | Expansion terminates within declared resource bounds |
| `det_parser.rs` | `DetParser.lean` | DPDA agrees with boolean decider (`headCheck_agrees`, `langCheck_agrees`) |
| `msg_tag.rs` | `DeterministicUnion.lean` | **`decidable_preserved`**, **`dcfl_preserved`**: installing a fresh-named dialect preserves DCFL membership (under `namesUnique`) |
| — | `Pipeline.lean` | End-to-end: `pipeline_success_grammar` (success ⟹ `ValidMessageGrammar`) |

### Headline theorems

- **`decidable_preserved`** / **`dcfl_preserved`**: installing a dialect with a fresh name into an agent with unique dialect names preserves decidability and DCFL membership of the agent's message language. (DCFL is a grammar-union closure property and is independent of R3, which is a semantic constraint on performative names; `install_preserves_core` and `install_no_core_redefinition` in `R3CorePreservation.lean` are the load-bearing R3 composition theorems.)
- **`agentDetParser_agrees`**: the concrete DPDA agrees with the boolean membership decider on all inputs.
- **`r1_mutual_sound`** + **`dfsNoCycle_complete`**: the DFS cycle detector is both sound and complete: it returns `true` iff no dependency cycle exists.
- **`check_acyclicity_iff_no_cycle`** / **`check_reachability_iff_all_reachable`** / **`check_performative_definedness_iff_all_defined`** / **`check_step_uniqueness_iff_no_duplicates`**: each R5 sub-check returns `[]` iff the corresponding contract property holds on the dialect's causal protocol.
- **`verify_monotone`** / **`verify_all_is_meet`** / **`verify_eventually_consistent`**: causal-protocol verification is a monotone map from the message-store join-semilattice into the three-valued verdict: monotone in the store, `(all …)` fan-in is exactly the eager meet, and replica verdicts join coordination-free under G-Set store merge (`verify M P S₁ ⊔ verify M P S₂ ⊑ verify M P (S₁ ∪ S₂)`). Merging knowledge can confirm but never overturn a per-replica verdict. (Coordination-freedom rests on the map being monotone, not on the verdict being a lattice — it is not; see below.)
- **`epp_correspondence`** / **`epp_correspondence_complete`**: the endpoint-projection correspondence, at run level. On a closed configuration, `project` and `glue` are mutually inverse and role-local verification is sound and complete for whole-conversation safety — so each endpoint checking only its own projection agrees with a verifier holding the entire conversation. The correspondence relates configurations (states), not executions.
- **`weakest_sound_condition`** / **`spliced_pred_permanently_unknown`**: role-local verification decides every message in a closed configuration exactly when every cited predecessor is role-local (`decidesAll ↔ predsLocal`); a message citing a non-local ("spliced") predecessor stays `Unknown` forever. This is the axiom-free half — no cryptographic assumption — pinning why causal locality is the condition role-local checking needs.
- **`temporal_bridge`**: every conformant execution, modelled as a monotone delivery schedule accumulating a closed configuration, embeds into the correspondence, so the state-level guarantee carries along conformant runs.
- **`causalTrace_regular`** / **`storeTrace_regular`**: the paper's DCFL-preservation proposition, mechanised with the deployed verifier's clause semantics (`verify_causal`'s disjunctive `Single`/`Any` pool and first-`(all …)` fan-in). Two trace languages, both recognised exactly by explicit finite automata over the canonical seen-set (the verifier's unbounded consumed-name list provably collapses onto sublists of the protocol's relevant names): the causal-order arrival language, and the order-free *store* language — which is the language the deployed valid-sticky verdicts actually accept (out-of-order arrival is `Unknown` then `Valid`, so acceptance is "every message eventually `Valid`"). `causalTrace_storeTrace` embeds the first in the second; regular ⊆ DCFL is formal (the automaton wrapped as a stack-untouched DPDA); and the projected protocol's recogniser is the same builder applied to the projected steps (`projection_adds_no_recogniser` — definitional by construction; the substantive local statement is the regularity instance). Role-local verification needs no machine class beyond what the global protocol already has.
- **`not_a_lattice`** / **`kmeet_is_glb`** / **`eager_absorption_fails`**: the three-valued verdict is a bounded meet-semilattice under the knowledge order — its GLB is the consensus meet (`Valid ⊓ Violation = Unknown` under that order) — while the deployed eager operators form a bisemilattice in which absorption fails. The two terminal verdicts have no join, so the verdict is provably **not** a lattice; the store, separately, is.
- **`openings_suffice`**: the safety verdict factors through predecessor presence and predecessor *types* only (`safety_reads_types_only`), so a delivery carrying exactly a predecessor's type yields the identical verdict to holding the full message. This is what licenses the typed field-opening (Merkle-over-fields, `typed_addr.rs`): selective disclosure is sufficient for role-local safety without revealing the rest of the message. (The Merkle construction itself lives in Rust; the Lean model proves the factoring, not the hashing.)
- **`resolvePerformative_scoped_custom`**: a custom performative resolves only against the dialect selected by its `(lang …)` wrapper. Other installed dialects cannot redirect it. `resolvePerformative_unscoped_custom` rejects custom names without a scope, and `resolvePerformative_no_fallback` rejects names absent from the selected dialect.
- **`pipeline_success_grammar`**: if the verified pipeline accepts a string, the result satisfies the `ValidMessageGrammar` relation.

Differential tests (`crates/cbcl-parser/tests/differential.rs`) run both implementations on the same test vectors and assert identical accept/reject verdicts.

## Architecture

Strict **purity boundary**: the core crates are deterministic, `no_std + alloc`, `#![forbid(unsafe_code)]`. Effectful code (I/O, CLI, WASM bindings, FFI) lives in shell crates that import the core, never the reverse. See `.hence/ADR-004-purity-boundary.md` and `.hence/PURITY-MAP.md`.

## Testing

- **Unit tests**: 862 in cbcl-core, 155 in cbcl-parser, 62 in cbcl-wasm, 36 in cbcl-erl (19 further ignored), 14 in cbcl-ffi; 4 CLI integration tests
- **Property tests**: 37 proptest cases (31 in cbcl-core, 6 in cbcl-parser) covering USDD verification properties
- **Differential tests**: 21 integration tests comparing Rust vs Lean on shared test vectors
- **Eventual-consistency / NFR tests**: 12 + 4 integration tests in cbcl-core
- **Fuzz targets**: libFuzzer harnesses for parser trust boundary
- **Mutation testing**: cargo-mutants config targeting critical-path modules (90% kill rate threshold)
- **Benchmarks**: Criterion benchmarks for parser, constraints, template expansion, gossip

## Contributing

Contributions are welcome, including reports of things that don't work or aren't clear. Bug reports live under [`bugs/`](bugs/) as Markdown with YAML frontmatter (severity S1-S4, priority P0-P2). Design specs (SPEC-001 onward) live under [`specs/`](specs/); architecture decisions are recorded in `.hence/`. In-flight work is tracked under [`plans/`](plans/).

Before opening a PR, run `cargo test --workspace`. For changes that touch verified modules, also run `lake build` from `lean-cbcl/`. If you're unsure how a change fits, open an issue or a draft PR; we're happy to help orient you.

## License

Apache-2.0. See [LICENSE](LICENSE).

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
