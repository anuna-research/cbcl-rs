# CBCL systematic comparison

The evidence does **not** support “nothing else does this.” Several established systems combine extensible messages with significant interaction, authentication or state semantics. What remains distinctive in this comparison is CBCL's proposed packaging: a small portable kernel, restricted runtime dialect installation, local role/causal checks and accepted-act state rules, with an optional certified resource layer. No examined source set establishes an exact replacement; that is a bounded finding, not a uniqueness proof.

The strongest comparisons are **BSPL** for business information protocols, **Scribble** for interaction types, **Arazzo** and **Aqua** for executable choreography, **Matrix/AT Protocol/Scuttlebutt** for authenticated distributed evidence/state, **KERI/ACDC** for portable verifiable data, and **Holochain** for agent-centric validation. Comparing CBCL only to blockchains would miss its closest neighbors.

## Feature matrix

Ratings refer to the inspected version and scope, not project quality. N=native, P=partial/profile dependent, E=external layer, X=outside design, ?=not established. “Behavior” does not imply safe restriction; “state” does not imply an immutable business-act log. See [[cbcl-comparison-method#Assessment ratings]].

| System | Neutral substrate | Dynamic vocabulary | Behavior extensions | Local causal checks | Signed evidence | Derived state | Evidence |
|---|---|---|---|---|---|---|---|
| CBCL | N | N | N | N | P | N | B01, B02, B03, B04, B05 |
| BSPL | N | P | N | N | E | P | S01, S02, S35 |
| Scribble | N | P | N | N | E | E | S03 |
| PACT | ? | ? | ? | ? | ? | ? | S04 |
| Daml/Canton | X | P | N | P | N | N | S05, S06 |
| Holochain | X | N | N | N | N | N | S07, S08, S09 |
| Goblins/OCapN | P | N | N | P | P | P | S10 |
| Agoric | X | N | N | P | N | N | S11, S12, S13 |
| ActivityStreams 2 | N | N | P | E | E | E | S30 |
| DIDComm | N | N | P | P | N | E | S15 |
| KERI/ACDC/CESR | N | N | P | P | N | P | S16, S17, S38 |
| WoT Thing Description | N | N | P | P | P | E | S31 |
| UBL/ebBP | N | P | N | N | E | P | S19, S37 |
| NLIP | N | P | P | P | ? | ? | S20, S21 |
| MCP | N | N | P | P | P | E | S22 |
| A2A | N | N | P | P | P | P | S23 |
| Accord Project | N | P | N | P | E | P | S24, S25 |
| Aqua/AIR | P | N | N | N | E | P | S26 |
| AsyncAPI | N | N | P | P | E | E | S27 |
| Arazzo | N | N | N | N | E | P | S28 |
| Matrix | P | N | P | P | N | N | S32, S33 |
| Secure Scuttlebutt | N | N | P | P | N | P | S34 |
| AT Protocol | P | N | P | P | N | N | S39, S40 |
| Bounded-counter CRDT | N | X | X | E | E | N | S36 |
| JSON | N | P | X | E | E | E | S29 |

## What the comparison changes

**BSPL exposes an actual CBCL language gap.** Immutable keyed parameter bindings, in/out/nil knowledge constraints and composition are not equivalent to checking field shapes and predecessor act types. A quoted value need not automatically bind an acceptance to that exact value in current CBCL. Proposed `bindings` syntax must remain labelled proposed. BSPL's general protocol analysis is also distinct from proofs for selected CBCL reference models. [BSPL implementation](https://github.com/shcv/bspl), [BSPL composition paper](https://www.csc2.ncsu.edu/faculty/mpsingh/papers/mas/AAMAS-12-BSPL.pdf).

**Arazzo is a serious workflow comparator.** It has step dependencies, runtime output bindings, success conditions, retries, workflow composition and asynchronous join points. Its security mechanisms are left to implementers. CBCL's intended distinction is independently checkable business-act acceptance and state, not the mere existence of declarative workflow semantics. [Arazzo specification](https://spec.openapis.org/arazzo/latest.html).

**Authenticated causal data and deterministic state are not novel by themselves.** Matrix supplies signed causal events and room-state resolution; AT Protocol supplies dynamic schema acquisition and signed deterministic record-map repositories; Scuttlebutt supplies signed per-author feeds. Matrix room rules are specialized, AT repositories contain mutable records, and none of those facts alone establishes CBCL-style bounded business dialect installation. [Matrix room-v7](https://spec.matrix.org/latest/rooms/v7/), [AT repositories](https://atproto.com/specs/repository), [AT Lexicon](https://atproto.com/specs/lexicon), [Scuttlebutt](https://ssbc.github.io/scuttlebutt-protocol-guide/).

**Portable verifiable data already has substantial machinery.** KERI/ACDC includes chained data, typed edges, schema/policy and disclosure; DIDComm defines authenticated messaging and protocol threading. CBCL needs a concrete interoperable authorization and canonical-evidence boundary to differentiate usefully here. [ACDC](https://trustoverip.github.io/kswg-acdc-specification/), [DIDComm](https://identity.foundation/didcomm-messaging/spec/).

**A thinner waist is a tradeoff.** Holochain, Daml/Canton and Agoric provide more operational machinery and stronger integrated application services at the cost of choosing a substrate. CBCL's host still has to supply transport, identity/key custody, storage and operational reliability. Optional counter validators are additional infrastructure. No mandatory CBCL native token is different from zero operating cost or no validator trust assumptions. [Holochain validation](https://developer.holochain.org/build/validation/), [Daml paper](https://arxiv.org/abs/2303.03749), [Agoric platform](https://docs.agoric.com/guides/platform/).

## Boundaries on CBCL claims

The current formal work establishes selected abstract properties, not end-to-end Rust/crypto/network equivalence. Consensus-free counter safety assumes the specified Byzantine threshold and quorum rules; asynchronous liveness additionally needs delivery, scheduling and resource/contention assumptions. Fair scheduling alone does not dissolve competing reservations. General author-dialect progress checking and immutable business-dataflow bindings are not implemented. Account-DAG/collective-model correspondence and Rust scheduler correspondence must not be silently promoted to complete proofs. See baseline B04–B09 in [[cbcl-comparison-sources#Local baseline]].

The `signed` wrapper is not itself authentication; the host must verify evidence. Unsigned dialect profiles exist. `application/cbcl` is a proposed media type in the repository IETF draft; this comparison does not establish an IANA registration. Restricted grammar does not by itself prove all behavioral safety properties. JSON has a decidable syntax and is not a Turing-complete execution language.

## Defensible positioning

> CBCL is a small, transport-independent language for defining and checking business messages, their causal rules and the state they produce, without requiring a shared ledger or native token.

Add “restricted runtime dialects” when explaining its technical differentiation. Avoid “first,” “unique,” “trustless,” “formally verified implementation” and “guaranteed live” without much narrower qualifications. The next useful design comparison is an identical quote/accept/pay protocol in CBCL, BSPL, Arazzo and a Matrix/AT implementation: measure which invariants each author writes, which runtime checks them, and which remain host obligations.

Detailed case boundaries: [[cbcl-comparison-cases]]. Collection, ratings and limits: [[cbcl-comparison-method]]. Sources and local hashes: [[cbcl-comparison-sources]]. Machine-readable evidence, sessions and Elephant exports are in `outputs/cbcl-comparison-evidence/`.
