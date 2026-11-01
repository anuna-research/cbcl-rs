# CBCL and BSPL: local source comparison

## Orientation

**BSPL is one of CBCL's closest language comparisons.** Both describe decentralized interactions between roles, leave business decisions to agents and do not intrinsically require a shared ledger or native token. BSPL is particularly strong at keyed information flow and business-data consistency. CBCL combines bounded dialect extension, explicit causal evidence and deterministic state rules, with optional certified resources. Neither subsumes the other in the inspected implementations.

The practical difference is visible in a quote acceptance: BSPL's context checks reject changing the known quoted price; CBCL's current shape and causal checks do not compare the acceptance price to its cited quote. Conversely, BSPL's inspected default receive path does not supply CBCL's authenticated accepted-history discipline or cryptographic predecessor evidence. Authentication remains an explicit host obligation in CBCL too.

This is Tier 4 comparative research, not a proposed specification change. Failure mode being corrected: equating all role/protocol languages, or assuming CBCL's causal checks imply immutable business-value bindings. Maintainer next action: decide whether keyed immutable bindings belong in CBCL, using the examples and constraints below. No language feature is implemented by this report.

Local BSPL is `/Users/anuna-02/Code/bspl` (`../bpsl` does not exist), clean HEAD `f48bac4ae9bbfb956fe7aa8264ded261a61583cc`. CBCL is `/private/tmp/cbcl-bounded-counter`, branch `state-rules-spec`, including existing uncommitted work. The source manifest records exact commits, paths and hashes. Findings apply to these snapshots, not every BSPL implementation or every published theory result. This refines [[cbcl-systematic-comparison]] and [[cbcl-comparison-cases]].

## The two models

```text
BSPL
  protocol + role's observed information, grouped by keys
      |
      +-- in:   sender already knows this parameter
      +-- out:  sender introduces a previously unknown binding
      +-- nil:  sender has not observed this parameter
      |
      v
  enabled messages -> agent chooses values/actions -> local adapter

CBCL
  installed dialect + message + explicit causal evidence + role cast
      |
      +-- bounded declarative templates and shape checks
      +-- thread-scoped predecessor identity/type checks
      +-- role/signer/recipient conformance, when enabled
      |
      v
  accepted act set -> deterministic state fold
      |
      +-- optional certified numeric-resource protocol
```

The arrows omit external application effects. Neither a protocol declaration nor an accepted message alone makes a bank transfer or physical shipment happen.

## Comparison table

| Dimension | BSPL at this checkout | CBCL at this worktree |
|---|---|---|
| Central abstraction | Information protocol: roles, keyed parameters, messages and knowledge adornments | Extensible performatives, shapes, causal contracts, roles, evidence and state |
| Agent autonomy | Protocol constrains what may be sent; Python/AgentSpeak policies choose what to do | Dialect constrains messages; host chooses actions and drives admission |
| Dependencies | A sender must know all `in` bindings; several messages can contribute knowledge | Named predecessor act types and explicit hashes; `(all …)` fan-in available |
| Business-value consistency | Concrete equality within matching key contexts | Field typing and causal evidence; no general native cross-act parameter-binding clause |
| Unknown versus absent | `nil` tests sender-local non-observation | Missing predecessor evidence yields `Unknown`/pending; not a general `nil` business-value feature |
| Instance correlation | One or more `key` parameters; hierarchical contexts in adapter | Thread, accepted root/cast, dialect identity and explicit content addresses; state keys are projection keys, not immutable BSPL keys |
| Concurrency | Independent knowledge-enabled sends, separate receptions; choices encoded through shared `out`/`nil` parameters | Causal partial order, optional role-local correspondence and choice checks; competing acts can remain as evidence |
| Composition | Protocol references with role/parameter substitution; public/private parameters; refinement checker | Dialect `extends`, ancestry resolution and bounded template composition; not equivalent to information-protocol substitution |
| Projection/locality | Role-oriented observations and protocol projection code | Optional role layer; strict profile enforces causal locality; role projection and selected Lean correspondence results |
| Static analysis | Path safety/liveness, Mambo queries/deadwood, optional SAT enactability/atomicity, refinement | R1–R7 well-formedness, resource/structural gates, selected Lean proofs; no general author-protocol completion checker |
| Runtime | Python adapter, knowledge store, enabled-message generation, reactions, policies, UDP/TCP components | Pure Rust core with parser and host bindings; explicit monitor/gate interfaces |
| Message evidence | Schema name, payload and metadata in inspected adapter | Canonical content identity, explicit predecessor references, signed wrappers/evidence mechanisms |
| Authentication | Not established by inspected default JSON/UDP receive path; custom transport could add it | Host must authenticate signer and complete semantic envelope; a wrapper is not authentication |
| Application state | Knowledge bindings and message history; policy code can compute other state | Closed declarative state-rule vocabulary, order/duplicate-insensitive folds over accepted acts |
| Money/resources | No native escrow/Byzantine counter primitive found in inspected grammar/runtime; host could implement one | Optional bounded counter, floor/ceiling, transfer/burn/mint and quorum-certified resource profile |
| Proof boundary | Executable analysis tools and repository tests; no whole Python-adapter proof established by this inspection | Lean reference-model proofs plus finite Rust correspondence tests; no complete end-to-end Rust/network proof |
| Grammar/extension safety | Restricted BSPL specification grammar via TatSu; agent policies remain general Python/AgentSpeak | Restricted dialect/template grammar and explicit depth/expansion limits; selected syntax-installation DCFL theorems |
| Ledger/token requirement | Neither is a language requirement | Neither is a language requirement; optional validators still require operation and trust assumptions |

## A purchase in actual BSPL syntax

The following parses and is exercised by the focused probe:

```text
Purchase {
  roles Buyer, Seller
  parameters out order key, out item, out price, out accepted

  Buyer -> Seller: Request[out order key, out item]
  Seller -> Buyer: Quote[in order key, in item, out price]
  Buyer -> Seller: Accept[in order key, in item, in price, out accepted]
}
```

`order` identifies the enactment. Request introduces the order and item. Seller must learn them before sending Quote, which introduces price. Buyer must learn price before sending Accept, and carries the existing item/price values. `accepted` is newly introduced information; its name does not itself force the Python value `True` or express payment conservation. The repository grammar does not attach primitive value types to these parameters.

At the protocol boundary, `out` marks what completion must produce, whereas message-level `out` marks what that message introduces to its sender's knowledge context. These are related but distinct levels. An `out` is not a mutable assignment: even assigning the same value again is blocked once that parameter is already bound in the sender's context, apart from duplicate handling. New key contexts permit new enactments.

The grammar additionally accepts protocol-level `any`/`opt`; message-level adornments are `in`/`out`/`nil`. Do not attribute complete optional-parameter semantics to every backend merely because the parser accepts these words. Source: BSPL `parsers/bspl/bspl.gr`, `protocol.py`, `adapter/store.py`.

### Where current CBCL differs

The executable CBCL probe declares `quote` and `accept`, numeric price shapes and `(protocol (then begin quote accept))`. A quote has price 100. An acceptance has price 1 and cites the exact quote's content address. Observed results:

```text
changed_price_missing_quote=Unknown
changed_price_with_quote=Valid
changed_price_shape_ok=true
```

That `Valid` is the **low-level causal verifier's result**, not a claim of complete authentication or full monitor admission. It establishes the causal link/type; shape checking separately establishes that 1 is a number. Neither establishes equality with the predecessor's 100. A host-supplied immutable gate could impose a bespoke price rule, but that is not a portable general native binding rule in today's dialect language.

Against a BSPL local history already containing the order/item and quote price 100, the actual adapter store returns:

```text
Accept(price=100): integrity=true,  emission=true
Accept(price=1):   integrity=false, emission=false
```

This is a concrete advantage of keyed immutable bindings, not evidence that BSPL checks arbitrary arithmetic or authenticates the remote supplier. It also does not prove that every receiver already knows the quote: consistency is checked against the receiver's actual context.

## Local knowledge is not cryptographic ancestry

A particularly useful contrast is a three-party handoff:

```text
A -- M(id, x) --> B -- N(id, x, y) --> C
```

BSPL allows B to send N after receiving M: B knows `id` and `x` and introduces `y`. C can learn `id` and `x` from N without directly observing M. The source probe confirms N is viable while C has observed no M.

In the corresponding CBCL **strict raw-edge role profile**, N cites M as predecessor, but C is not an endpoint of M. R6 reports:

```text
NotCausallyLocal { performative: "n", predecessor: "m", role: "c" }
```

The condition buys C the ability to verify its causal obligations from its own visible evidence. The price can be recipient widening or explicit evidence delivery. CBCL also has envelope/evidence-widening mechanisms: this probe does not establish that every CBCL profile must disclose M's full payload or that the handoff is inexpressible. It pinpoints a difference between sender-local information enablement and independently checkable predecessor evidence. See [[causal-locality]], [[endpoint-projection]] and [[SPEC-015-evidence-widening-v2]].

There is no automatic semantics-preserving translation in either direction. Turning `in price` into “cite a quote” loses value consistency; turning explicit predecessor identity into “someone conveyed these fields” loses evidence identity and origin. A translator must make the trust boundary explicit.

## Concurrency and choices

BSPL permits independent emissions when their knowledge constraints allow them. Send and receive are separate abstract events, so no central sequencer is inherent in the model. Choice can be represented by one role introducing a shared result, or by complementary `nil` requirements.

However, `nil` is **local absence**, not a globally unique reservation. In the tested NilRace, A sends L with `nil right`; before B receives L, B may still send R with `nil left`. The probe confirms both local conditions can hold. Thus `nil` is not an asynchronous compare-and-swap or a double-spend defense. Whether a surrounding protocol is safe depends on its whole information structure and the particular invariant checked.

CBCL's causal `(any …)` also must not be promoted to global mutual exclusion. Generic causal validation and state folds can preserve competing acts; quorum-certified counter choices are a separate, stronger mechanism with explicit validator assumptions. The [[protocol-progress]] example deliberately retains competing ticks rather than electing a winner. Both languages need careful design to turn a declared choice into the business invariant the application actually wants.

## Composition, reuse and refinement

BSPL resolves nested protocol references, maps actual roles/parameters positionally and preserves message adornments during instantiation. Protocol-level public/private parameters define the information interface. This is a genuine semantic reuse mechanism, not textual concatenation. But shared outputs, keys and knowledge dependencies can introduce problems; successful parsing/reference resolution is not proof that a composition is safe/live. The inspected `validate_protocol_composition` function is a placeholder, while other parameter and reference checks do run.

The repository also implements refinement by enumerating paths and comparing public-parameter producer sources and role knowledge, recursively respecting prefixes and checking completion/branch conditions. The existing example confirms Ship-First refines Flexible-Purchase. This is **information-protocol refinement**, not proof that arbitrary generated Python or CBCL Rust implements the specification. The implementation exposes a module function; its presence does not mean every CLI command invokes it.

CBCL `extends` and template expansion solve vocabulary inheritance and safe expansion. They do not supply the same protocol interface substitution or information-based refinement test. This is another area where BSPL has useful design ideas beyond a different surface syntax.

## What the verification tools actually establish

BSPL's path engine tracks abstract message schemas, emission/reception events, role knowledge and key-name contexts. It does not enumerate arbitrary concrete prices, identifiers or Python callback behavior. Its safety predicate looks for conflicting producer roles for parameters. The path implementation groups multi-key conflicts by **key-name sets**, not concrete key values. The SAT backend's parameter cover is name-based and differs from that grouping. Do not describe the backends as proven equivalent complete analyses of every multi-key execution.

The path liveness check searches maximal abstract paths for missing required public outputs. It is closer to “no incomplete maximal enactment in this model” than to “every real agent will eventually act.” The SAT `correct` formula explicitly includes non-lossy transmission; its completion predicate refers to reception of output-producing messages. Neither establishes real-time progress under crashes, permanent packet loss, arbitrary Byzantine actions or unfair scheduling. These distinctions matter even when a tool prints `live: True`.

The focused tests deliberately demonstrate both directions: Purchase is reported safe/live; competing producers yield unsafe with a witness; circular knowledge dependencies yield nonlive with a witness. The nonlive result's `incomplete` diagnostic is empty in this checkout because it subtracts required outputs from the already-known subset; the boolean result is still false. This is a diagnostic implementation caveat, not a refutation of the language's liveness concept.

CBCL has stronger selected machine-checked model results in other dimensions: finite syntax-installation recognition, causal verdict/evidence properties, local/global role correspondence, order/duplicate-invariant state and selected counter refinements. It does **not** offer a general user-dialect liveness/refinement analyzer equivalent to BSPL's tools. Its counter liveness work has explicit assumptions; it is not evidence of completion for arbitrary business dialects. Lean model proofs are not a universal correctness proof of the Rust implementation. See [[SPEC-018-dcfl-installation]], [[SPEC-019-state-rules]] and `lean-cbcl/README.md`.

## Runtime and security: do not confuse model with enforcement

BSPL includes a substantial enactment adapter: enabled-message matching, keyed history, reactions, scheduling, policies, forwarding/reminders and application integration. It is not merely a parser and paper. General Python/AgentSpeak code supplies decisions and external effects. Its default transport code serializes JSON and uses UDP; alternative components/hooks exist. No signature or hash-chain verification appears in the inspected default receive route. That is a scoped source finding, not a claim that BSPL applications cannot add authenticated transport.

The default `Adapter.receive` checks duplicate identity and equality with existing local context, then stores and signals reception. The probe supplies an Accept on an unseen order without a prior quote and observes storage plus ReceptionEvent. This is compatible with receiving new information; it is not a claim that a legitimate receiver must possess all of the sender's knowledge. It shows that this receiver does not independently prove the remote sender followed its `in` obligations or authenticate the origin.

A separate method-level reproduction shows `Store.check_dependencies` returning true when only the first iterated `in` parameter is known. The function returns immediately on that first match, so remaining inputs are not checked on that path. Its TODO acknowledges incomplete logic. This reproduction invokes the actual method with an actual schema and explicit partial Context; **it is not a full-network exploit or an end-to-end Adapter.send reproduction**. Keep the language guarantee and this Python implementation limitation separate.

CBCL's strict AdmissionMonitor separates authenticated receipt from acceptance, considers only accepted predecessors and retains/reconsiders unresolved candidates. It requires a host AdmissionGate that authenticates signer and complete envelope, including cast/thread/dialect context. There is no default accepting gate. Hosts still must drive scheduling, supply storage/transport and enforce immutable syntax/shape obligations at the gate. Other lower-level APIs are not equivalent to this strict monitor.

The fair comparison is therefore not “BSPL trusts messages, CBCL has signatures so it is trustless.” It is: BSPL information compliance and CBCL accepted-evidence compliance place different obligations on the implementation, and the inspected default paths enforce different subsets.

## State and bounded resources

BSPL's key contexts are native protocol state: knowledge bindings and observed messages. It would be wrong to say BSPL has no state. The narrower difference is that CBCL provides named application-state projections with specified conflict handling and common Rust/host binding semantics. BSPL application code can compute totals, balances or views, but this checkout's grammar/runtime does not expose the same closed state-rule algebra as a language primitive.

Similarly, a BSPL parameter called `balance` or `paid` does not enforce numeric conservation. CBCL's bounded counter adds escrow rights and optional Byzantine quorum certification, including a ceiling when configured. This resource profile carries assumptions and operational machinery beyond ordinary messages. It does not make all CBCL protocol choices Byzantine-safe, and it does not imply consensus is necessary for BSPL's ordinary information protocols.

Neither grammar requires a cryptocurrency or mandatory common ledger. CBCL's smaller host-neutral kernel and BSPL's Python enactment toolkit are implementation/deployment differences; BSPL's language itself is also a relatively small declarative protocol layer.

## LangSec and extensibility

Both use explicit restricted specification grammars. BSPL defines finite message/role/parameter declarations and protocol references in TatSu. It is not a Turing-complete protocol specification merely because agents are implemented in Python. CBCL's syntax is S-expressions with bounded, nonrecursive dialect substitutions and separate well-formedness checks. A formal syntax-language class alone establishes neither immutable value consistency nor runtime authentication.

CBCL's per-installed-environment syntax preservation theorem is a specific result. This inspection establishes no equivalent formal language-class theorem for BSPL, but absence of such evidence does not imply its grammar is undecidable or unsafe. No meaningful parser security ranking follows solely from comparing brace syntax to Lisp syntax. Parsing costs, hostile input limits, semantic validation and actual implementation correspondence need separate evidence.

## What CBCL should learn from BSPL

1. **Keyed immutable business bindings.** Give dialect authors a native way to require order/price/currency equality across specified acts. Make key scope, value origin, conflicting introductions and out-of-order evidence explicit.
2. **Knowledge-based interfaces and composition.** Distinguish values a subprotocol requires from those it produces. Check compositions instead of assuming ancestry reuse establishes business compatibility.
3. **Author-facing counterexamples.** A checker showing a dead-end or conflicting producer path can be more actionable than a generic installation error. Keep its model assumptions visible.
4. **Separate safety categories.** Report syntax/resource safety, information consistency, causal authenticity, numeric invariants and progress separately. “Safe protocol” is too broad without a named property.

Adopting bindings would be a semantic change, not a shape-check convenience. A global mutable equality table or a “first received wins” binding would make replicas depend on arrival order. A global “not yet known” gate can invalidate prior decisions when evidence grows. Any proposal must preserve or explicitly revise CBCL's admission/state separation, evidence monotonicity and role-local correspondence. Binding evidence should name the relevant key scope and origin act(s); conflicts and duplicate introductions need defined treatment. No unimplemented syntax is presented as supported here.

The useful pitch is: **BSPL makes distributed business information dependencies explicit; CBCL makes bounded message dialects, causal evidence and derived state explicit.** They are close enough that a serious CBCL design should explain which BSPL guarantees it preserves, adds or leaves to the host.

## Source-reading map

These are local source paths at the pinned revisions, not external web claims. Functions provide stable search targets when line numbers move. Exact bytes are hashed in `source-pins.json`.

| Claim | BSPL source | CBCL source |
|---|---|---|
| Grammar and adornments | `src/bspl/parsers/bspl/bspl.gr` | `docs/cbcl-grammar.ebnf`, `crates/cbcl-parser/src/dialect_parser.rs` |
| Concrete equality and output/absence checks | `adapter/store.py:157`, `check_integrity`, `check_outs`, `check_nils` | `shape.rs`, `ShapeConstraint::check`; `protocol.rs:598`, `verify_causal` |
| Local knowledge and handoff | `verification/paths.py:43`, `known`; `viable` | `r6.rs`, `r6_violations`; `projection.rs`, `verify_causal_for_role` |
| Receive/authentication boundary | `adapter/core.py:183`, `Adapter.receive`; receiver/emitter modules | `admission.rs:22`, `AdmissionGate`; `AdmissionMonitor::receive/step` |
| Dependency implementation caveat | `adapter/store.py:189`, `check_dependencies` | Not a claim about CBCL |
| Subprotocol substitution | `protocol.py:348`, `resolve_references/instance` | `dialect.rs`, registry ancestor resolution; `template.rs` |
| Composition validation boundary | `validation.py`, `validate_protocol_parameters/validate_protocol_composition` | R1–R7 modules; no asserted generic information-composition equivalence |
| Refinement | `verification/refinement.py`, `subsumes/refines`; `tests/test_refinement.py` | `lean-cbcl/README.md`, specified model-refinement boundaries |
| Path safety/liveness | `verification/paths.py:658`, `liveness/safety`; `max_paths` | Different properties: R5/R6 and Lean modules described in README |
| SAT assumptions and backend differences | `verification/sat.py:186`, `unsafe`; `correct`; `non_lossy`; `complete` | No SAT-equivalent checker claimed |
| State and resource semantics | `adapter/store.py`, knowledge Context; no matching rule syntax in inspected grammar | `state.rs`, `r7.rs`, `intend.rs`, `quorum/README.md` |

BSPL paths in this table are relative to `src/bspl/` unless a longer prefix is written. CBCL module paths without prefixes are relative to `crates/cbcl-core/src/`. This is a reading map, not a substitute for the executable examples or for inspecting a whole function's assumptions.

## Validation, reproducibility and limits

Unmodified BSPL source was copied to a temporary sandbox to avoid writing generated parser files into the checkout. A separate Python environment used declared dependencies plus `croniter` (imported by the adapter but absent from setup.cfg's direct list) and test tooling. Initial collection failures and missing historical sample filenames are retained rather than hidden. Optional `boolexpr` SAT tests were not run. A final selected path/refinement/store/adapter test run passed; exact totals are in `bspl-source-comparison-evidence/pytest-final.log`, not a claim that the whole upstream suite passes. One broad sample-liveness traversal was deselected; focused positive/negative liveness probes were executed separately.

CBCL parser/core were rebuilt offline before the Rust probe; build log, linked-artifact hashes and assertions are retained. The probe covers low-level shape/causal checks and an R6 violation, not a fully authenticated multihost execution. No TPS comparison was attempted. No production code or BSPL source was changed.

Evidence directory: `outputs/bspl-source-comparison-evidence/`. It includes the executable purchase, both probe sources/results, selected test logs including failed attempts, dependency freeze, source manifests, and signed Elephant findings. Independent source/claim review is recorded in [[cbcl-bspl-source-review]]. This is a source audit and focused experiment, not a complete verification of either implementation.
