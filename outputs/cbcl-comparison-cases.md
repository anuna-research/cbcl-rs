# Comparison cases

Every entry is scoped to the cited captured sources. Ratings do not assert impossibility outside that scope.

## CBCL

Restricted dialect installation and accepted-act state; host supplies authentication and persistence. General immutable parameter bindings and general liveness checking remain gaps. Evidence: B01, B02, B03, B04, B05.

## BSPL

Strongest information-protocol comparison: keyed immutable bindings, in/out/nil knowledge flow, composition and protocol analysis. Parameter knowledge is richer than current CBCL value guards. Evidence: S01, S02, S35.

## Scribble

Global interaction types, role projection and recursion; compare communication conformance, not an authenticated state-fold kernel. Evidence: S03.

## PACT

Paper retained as a lead; not scored without a full-paper implementation and semantics audit. Abstract-only coverage cannot establish equivalence. Evidence: S04.

## Daml/Canton

Ledger-backed contracts, authorization, privacy and atomic transactions. More integrated execution substrate; not transport-neutral accepted-message semantics. Evidence: S05, S06.

## Holochain

Agent-centric runtime with source chains and DHT validation. No mandatory global total order, but applications use Holochain machinery. Countersigning unstable/off by default in 0.4+. Evidence: S07, S08, S09.

## Goblins/OCapN

Distributed object-capability actors; authority through references and general Scheme behavior, rather than a restricted business-message kernel. Persistence and transport profile matter. Evidence: S10.

## Agoric

Hardened JavaScript, ERTP assets and Zoe contracts; broad execution/platform and economy. Strong asset safety concepts, different deployment waist. Evidence: S11, S12, S13.

## ActivityStreams 2

Extensible vocabulary and normative core semantics. Extension processing has no normative general model; unknown extensions are ignored. Editor-copy evidence. Evidence: S30.

## DIDComm

Transport-independent authenticated/encrypted messaging and threading; application protocols supply their business state semantics. Evidence: S15.

## KERI/ACDC/CESR

Chained verifiable credentials, typed edges, rules/policy, disclosure and registry state. Much closer to portable evidence than a plain schema format; general business conformance not established here. Evidence: S16, S17, S38.

## WoT Thing Description

Interaction affordances, schemas, security metadata and protocol bindings; evidence is the 2.0 editor draft, not a claim about published 1.1. Evidence: S31.

## UBL/ebBP

Business documents plus business-process collaboration/choreography. Requires execution/security bindings; not merely invoice field schemas. Evidence: S19, S37.

## NLIP

ECMA transport-neutral AI-agent application messages plus bindings. Suite publication evidence does not establish full runtime or business-invariant coverage. Evidence: S20, S21.

## MCP

Version-pinned 2025-11-25 interface/lifecycle snapshot. Tools, resources, schemas and authorization are meaningful protocol semantics, not an arbitrary replicated business state machine. Evidence: S22.

## A2A

Version 1.0.0 task lifecycle, artifacts and extensions; distinguishes task coordination from causal business-act acceptance and certified resources. Evidence: S23.

## Accord Project

Current TypeScript contract logic and templates can be ledger independent. Legacy Ergo is a separate restricted language; do not attribute its properties to current TypeScript. Evidence: S24, S25.

## Aqua/AIR

Distributed choreography and pure state-transition interpreter. A close executable interaction-language comparator; operational maturity and full security/proof correspondence not established. Evidence: S26.

## AsyncAPI

Message/API interface definitions and bindings. Workflow behavior is scored separately under Arazzo. OpenAPI remains an unscored contextual lead without a separate capture. Evidence: S27.

## Arazzo

1.1.0 workflows: dependencies, output binding, conditions, retries, composition, async joins. Security mechanisms left to implementers; no established signed accepted-act-set fold. Evidence: S28.

## Matrix

Signed causal event graph and deterministic room-state resolution are strong prior art. Room-v7 rules are specialized; custom event types do not install arbitrary bounded business authorization. Evidence: S32, S33.

## Secure Scuttlebutt

Signed hash-linked per-author feeds and application messages. No global act DAG or general safe business-state installation established. Evidence: S34.

## AT Protocol

Dynamic Lexicon schemas plus signed deterministic map repositories. Mutable record map, not append-only causal business acts; validation of unknown schemas is policy dependent. Evidence: S39, S40.

## Bounded-counter CRDT

Escrow numeric bounds without global ordering are established prior art under trusted-replica assumptions; not the Byzantine-certified CBCL profile. Evidence: S36.

## JSON

Interchange grammar, not a business execution/authorization language. JSON syntax is decidable; calling it Turing complete is incorrect. Evidence: S29.

## Comparison by invariant and trust boundary

### Business dataflow: CBCL versus BSPL

The relevant experiment is not whether both can name `quote`, `accept` and `pay`. It is whether accepting a quote binds the order key, seller, buyer, price and currency to the exact earlier values, and whether independently delivered messages can introduce conflicting bindings. BSPL's parameter knowledge and keys directly address this class of constraint (S01/S35). Current CBCL role/causal checks and field shapes address a different subset: predecessor type, role authorization and structural validity do not generally establish equality of every business value. A bespoke host check can close a particular gap, but that changes what the portable dialect itself guarantees.

CBCL's runtime restriction and formal syntax-installation result are meaningful additional dimensions, not a replacement for dataflow semantics. Conversely, a BSPL protocol verifier is not automatically a proof of signatures, storage durability or Byzantine money conservation. Compare these layers separately. A next-stage example should deliberately alter only the accepted price and show each implementation's verdict, then test concurrent duplicate order keys and out-of-order delivery.

### Workflow semantics: Arazzo, Aqua and Scribble

Arazzo 1.1.0 (S28) provides observable workflow semantics: dependencies, outputs, expressions, conditions, retries, jumps and asynchronous joins. Therefore “OpenAPI-family documents only describe shapes” is false once Arazzo is included. Its workflow executor observes operations and applies control flow; the inspected specification leaves security mechanisms to the implementer. The report's native local-conformance rating is at this executor scope, not a claim of CBCL-equivalent distributed authorization.

Aqua's AIR interpreter (S26) describes pure state transitions and distributed choreography. It deserves an executable example comparison, not dismissal as a transport SDK. This survey does not establish current production maintenance, complete failure semantics or proof correspondence. Scribble (S03) targets global interaction descriptions and endpoint projection, including recursion. Recursive protocol expressivity is distinct from immutable business value constraints and derived economic state. None should be described as “less expressive” without naming the dimension.

### Authenticated state: Matrix, AT Protocol and Scuttlebutt

Matrix room-v7 (S32) establishes a strong counterexample to novelty claims about signed causal events plus deterministic derived state. Its event authentication and state-resolution algorithm are specific to a room version. Allowing custom event types is not the same as letting a user install a new bounded authorization calculus. Client-server API capture S33 supplies the broader event-type context; the room-v7 evidence must not be presented as the current default version.

AT Protocol (S39/S40) dynamically resolves Lexicon schemas and signs deterministic repository maps. The same final map gives a canonical tree root independently of edit order; this is significant deterministic state, not merely arbitrary JSON blobs. It remains a mutable record map rather than an append-only history of accepted causal business acts. Unknown-schema validation has policy choices, including optimistic behavior; dynamic discovery is not equivalent to mandatory fail-closed semantic verification. Identity/key rotation and historical-commit verification also need an explicit historical trust policy.

Scuttlebutt (S34) signs per-author hash-linked feeds and supports application-defined message content without requiring a global ordered ledger. It is not a single global DAG of business acts; application semantics remain a separate layer. These examples suggest CBCL could be carried over existing evidence networks, but this report implements or proves no such integration.

### Portable evidence: KERI/ACDC, DIDComm and ActivityStreams

ACDC (S16/S17/S38) has schema-linked data, typed edges, policy/rule content and disclosure mechanisms. Calling it only a credential schema would erase important overlap with business evidence. The comparison leaves general CBCL-style causal business conformance partial, because the inspected documents do not establish identical executable acceptance rules. ToIP publication approval and the particular captured editor versions are separate status facts.

DIDComm (S15) provides real security envelopes and protocol-threading semantics while allowing transport independence. That is a natural carrier/integration comparator, not proof that CBCL itself performs key custody or authenticates every wrapper. ActivityStreams (S30) has normative core semantics and vocabulary extensibility, but no normative general extension-processing model; unknown extensions are ignored. Distinguish extending what a message says from installing enforceable behavior. The captured source is an official editor copy because the publication page was blocked.

### Application platforms and authority

Holochain (S07–S09) supplies agent-centric validation, source chains and DHT machinery, substantially reducing the host implementation burden relative to a portable kernel. Lack of global consensus does not mean absence of coordination: countersigning adds a particular coordination path and is unstable/off by default in the cited 0.4+ context. Daml/Canton (S05/S06) supplies ledger contracts, privacy and atomic transaction semantics; CBCL selective evidence handling is not an equivalent privacy guarantee.

Goblins (S10) restricts authority using object-capability references. A CBCL role check over a signed message is not automatically an object capability and does not inherit all ocap confinement properties. Agoric (S11–S13) combines capability-oriented Hardened JavaScript, assets and contract machinery in a broader platform. General-language safety discipline differs from accepting a restricted behavioral grammar. Current Accord contract TypeScript (S24) likewise must not inherit claims about legacy restricted Ergo (S25).

### Numeric resources and progress

The bounded-counter CRDT paper (S36) establishes escrow-based numeric invariant preservation without requiring global ordering under its replica assumptions. CBCL's optional Byzantine certification changes the adversary and quorum assumptions, not the historical existence of escrow counters. Resource safety, message authenticity, general protocol conformance and eventual completion are separate claims.

For CBCL, the particular quorum profile needs its stated n=3f+1 and q=2f+1 assumptions. Honest validators intersect conflicting certified choices in the relevant model; eventual useful completion additionally needs delivery/scheduling assumptions and an executable enabled path. Contending reservations can prevent a certificate even with fair scheduling. The Lean scheduler result applies to its reference model, not automatically to Rust worker queues, real packet loss or durable-journal behavior. Neither a generic platform's liveness claim nor a microbenchmark fills that proof gap.

### Remaining leads and publication limits

NLIP suite announcement/overview (S20/S21), PACT's abstract (S04), and the inspected MCP/A2A snapshots are retained to prevent premature closure. They are not uniformly full-spec audited. OpenAPI itself lacks a separate capture here; S27 is AsyncAPI and S28 is Arazzo. WoT evidence is a 2.0 editor draft, not a substitute for proving every statement about published TD 1.1. This is a systematic comparison rubric over a purposive corpus, not an exhaustive systematic literature review. Native token absence is not an audited per-project economics finding in this matrix.
