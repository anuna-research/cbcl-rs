---
id: SPEC-002
title: Structural Contracts for CBCL — Causal Protocols and Shapes
status: draft
version: 0.1.0
date: 2026-03-21
author: Anuna Research (https://anuna.io)
supersedes: SPEC-001 (DFA-based protocols)
prior-art:
  - Honda 1993 (binary session types — send, recv, end, duality)
  - Honda/Vasconcelos/Kubo 1998 (choice, recursion, multiparty)
  - Gay & Hole 2005 (subtyping, guardedness/contractivity)
  - Wadler 2012 (propositions as sessions — linear logic correspondence)
  - Caires & Pfenning 2010 (session types as intuitionistic linear propositions)
  - Ameloot/Neven/Van den Bussche 2011 (CALM theorem — monotonic = coordination-free)
  - Hellerstein 2019 (Keeping CALM — CACM survey, practical applications)
  - Bailis et al. 2015 (coordination avoidance, invariant confluence)
  - Conway et al. 2012 (logic and lattices for distributed programming, BloomL)
  - Shapiro et al. 2011 (CRDTs — conflict-free replicated data types)
  - Lamport 1978 (happened-before, causal ordering)
  - Mattern 1989, Fidge 1988 (vector clocks)
  - Birman/Schiper/Stephenson 1991 (lightweight causal broadcast)
  - Gan & Kuper 2022 (verified causal broadcast in Liquid Haskell)
  - Honda/Yoshida/Carbone 2008/2016 (multiparty asynchronous session types)
  - Montesi 2013 (choreographic programming — deadlock-freedom by construction)
  - Alur & Madhusudan 2004 (visibly pushdown languages)
  - Moore 2016 (software contracts for security — correct blame, complete monitoring, capability contracts)
  - Findler & Felleisen 2002 (higher-order software contracts, blame)
  - Dimoulas, Tobin-Hochstadt & Felleisen 2012 (complete monitors for behavioral contracts)
  - Demers et al. 1987 (epidemic dissemination)
  - Girard 1987 (linear logic)
  - Castellani/Dezani-Ciancaglini/Giannini 2024 (event structure semantics for multiparty sessions — causal structures over state machines)
  - Sanjuan/Poyhtari/Teixeira/Psaras 2020 (Merkle-CRDTs — Merkle-DAGs meet CRDTs, content-addressed causal ordering)
  - Kuper 2015 (LVars — lattice-based deterministic parallelism, monotonic writes, threshold reads)
  - Meiklejohn & Van Roy 2015 (Lasp — lattice-based coordination-free programming with CRDTs)
  - Neykova/Bocchi/Yoshida 2017 (decentralised runtime monitoring of multiparty sessions — DFA-based, the baseline SPEC-002 departs from)
  - Neykova & Yoshida 2014/2017 (multiparty session actors — session types for the actor model)
  - Tse 2017 (validating session protocols — LangSec workshop, DFA-based session validation)
  - Bauer/Leucker/Schallhart 2011 (Runtime Verification for LTL and TLTL — canonical three-valued LTL₃ verdicts)
  - Bartolo Burlò/Francalanza/Scalas 2021 (On the Monitorability of Session Types — closest prior work on dimensions of session monitoring + three-valued verdicts, but DFA-style monitors over in-order channels)
  - Cano/Mezzina/Pérez 2017 (Causally consistent reversible choreographies — monitors-as-memories, causal histories embedded in monitors)
  - Rowicki/Francalanza/Scalas 2025 (Correct Black-Box Monitors for Distributed Deadlock Detection, OOPSLA2 — newer Francalanza/Scalas distributed monitor, binary-verdict liveness only)
  - Hellerstein 2026 (The Coordination Criterion, arXiv:2602.09435 — modern spec-level statement of monotonicity ⇔ coordination-freedom)
  - Waites 2026, Plumbing (Leith Document Company) — contemporary convergent work
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-002: Structural Contracts for CBCL — Causal Protocols and Shapes

## Overview

CBCL guarantees syntactic safety — every message, including dialect definitions, is parsed by a deterministic pushdown automaton in bounded time. But syntactic safety is not protocol correctness. A message can parse successfully and still violate the interaction pattern a dialect author intended.

This specification adds **structural contracts** to CBCL dialect definitions. A structural contract constrains agent communication across two orthogonal dimensions:

- **Protocols** constrain the causal structure of message exchanges — which message types may follow which, expressed as dependency declarations rather than state machines.
- **Shapes** constrain the structure of individual messages — which parameters must be present, their types, and nesting depth.

Both dimensions are **monotonic** in the sense of the CALM theorem (Ameloot, Neven & Van den Bussche 2011): checking a protocol constraint is a positive assertion about immutable causal links between messages; checking a shape constraint is a positive assertion about the structure of an expanded S-expression. Neither requires mutable state, message ordering, or coordination between agents. This is a deliberate departure from SPEC-001, which used DFA-based protocol checking and required message ordering (ADR-004 in that spec). Protocols support both fan-out (multiple successors) and fan-in (merge/join via `(all ...)` — multiple predecessors verified conjunctively), both of which are monotonic on the append-only message store.

Structural contracts are optional. R1–R4 remain sufficient for safety. Structural contracts add protocol correctness as a separable layer: a SHOULD, not a MUST.

### Design Provenance

This specification synthesises ideas from several research threads, listed in order of directness of influence on the design.

**Session types.** Honda (1993) introduced binary session types — typed channels where `send T . S` and `recv T . S` describe a protocol's steps, with duality as an involution. Honda, Vasconcelos & Kubo (1998) added choice and recursion. Gay & Hole (2005) formalised guardedness. Wadler (2012, *Propositions as Sessions*) established the Curry-Howard correspondence: propositions in classical linear logic correspond to session types, proofs to processes, cut elimination to communication. Our protocol step declarations originate from Honda 1993; the causal dependency reformulation is new.

**The CALM theorem.** Ameloot, Neven & Van den Bussche (2011), with the formal proof in the PODS 2011 proceedings; popularised by Hellerstein's CACM survey (2019, [*Keeping CALM: When Distributed Consistency is Easy*](https://arxiv.org/abs/1901.01930)) and most recently restated by Hellerstein (2026, [*The Coordination Criterion*](https://arxiv.org/abs/2602.09435)). CALM states: a distributed program has a consistent, coordination-free implementation if and only if it is monotonic. The 2026 restatement frames the criterion at the specification level: an outcome admits a coordination-free implementation iff it evolves monotonically as the Lamport history is causally extended. Monotonic programs accumulate beliefs; their output depends only on the content of input, not the order of arrival. SPEC-001's DFA-based protocol checking was non-monotonic (stateful — the set of valid next messages depends on current state). This specification reformulates protocol checking as **causal dependency verification**, which is monotonic: each check is a positive assertion about immutable facts (message existence and type). By CALM, this is coordination-free — no message ordering, no Lamport clocks, no consensus required. The Coordination Criterion is the spec-level theorem; SPEC-002 instantiates it at the runtime-monitor level.

**Coordination Avoidance.** Bailis, Fekete, Franklin, Ghodsi, Hellerstein & Stoica (2015, [*Coordination Avoidance in Database Systems*](https://arxiv.org/abs/1402.2237)) introduce *invariant confluence* (I-confluence): a necessary and sufficient condition for coordination-free execution that preserves application invariants. CBCL's protocol invariants ("pause-ack must be caused by pause") are I-confluent — verifying the invariant depends only on the referenced message's existence and type, both of which are immutable facts. I-confluent invariants can be checked without coordination; non-I-confluent invariants (e.g., uniqueness, counting) cannot. This provides a finer-grained criterion than CALM alone: CALM tells you *monotonic = coordination-free*; I-confluence tells you *which specific invariants* qualify.

**CRDTs.** Shapiro, Preguiça, Baquero & Zawirski (2011, [*Conflict-free Replicated Data Types*](https://inria.hal.science/inria-00609399v1/document)) formalised data structures that converge without coordination. CBCL's dialect registry is a G-Set (grow-only set) CRDT — dialect installation is monotonic (set union, never retraction). The message store is an append-only log — structurally a G-Set of (message-id, performative, caused-by) triples. State-based CRDTs require only eventual delivery with a merge function (join on the lattice); no causal delivery middleware needed. SPEC-002's architecture is state-based: the message store is the state, append is the merge, verification is a local predicate on the merged state.

**Logic and Lattices.** Conway, Marczak, Alvaro, Hellerstein & Maier (2012, [*Logic and Lattices for Distributed Programming*](https://dl.acm.org/doi/10.1145/2391229.2391230)) extend the Bloom language with lattice types, showing that monotonic programs over lattices are automatically eventually consistent. CBCL's data structures map onto this framework: the dialect registry is a set lattice (join = union); the message store is a list lattice (join = append); protocol declarations are constants (trivially a lattice). The verification predicates (causal check, shape check) are monotone functions on these lattices — they cannot retract a previously true result when the lattice grows. This is the algebraic structure underlying the CALM guarantee.

**Causal ordering.** Lamport (1978, *Time, Clocks, and the Ordering of Events in a Distributed System*) defined the happened-before partial order. SPEC-002's `:caused-by` parameter is an explicit encoding of happened-before — rather than inferring causal order from vector clocks (Mattern 1989, Fidge 1988) or relying on causal broadcast middleware (Birman, Schiper & Stephenson 1991, [*Lightweight Causal and Atomic Group Multicast*](https://www.cs.cornell.edu/courses/cs614/2003sp/papers/BSS91.pdf)), each message declares its own causal predecessor. This moves the burden from the transport layer to the message format, eliminating the need for vector clocks or causal delivery guarantees. Verified causal broadcast has been mechanically proven correct in Liquid Haskell (Gan & Kuper, 2022); our Lean 4 formalisation targets a simpler property (causal link validity on an append-only store) using the same verification philosophy.

**Visibly pushdown languages.** Alur & Madhusudan (2004) defined VPLs as a subclass of DCFL closed under intersection. S-expression syntax maps directly onto the VPL alphabet partition. Shape constraints are VPL tree patterns. Shape checking is monotonic (positive assertions on immutable tree structure), complementing the monotonicity of causal protocol checking.

**Multiparty asynchronous session types.** Honda, Yoshida & Carbone (2008/2016, [*Multiparty Asynchronous Session Types*](https://dl.acm.org/doi/10.1145/2827695)) extend binary session types to multiparty with asynchronous communication, introducing global types projected to local types. Causal ordering of messages under asynchronous semantics is "subtle" (their word) — exactly the problem SPEC-002 addresses by making causality explicit. This specification is binary only; if extended to multiparty, Honda/Yoshida/Carbone's projection mechanism would be the starting point.

**Choreographic programming.** Montesi (2013, [*Choreographic Programming*](https://www.fabriziomontesi.com/files/choreographic_programming.pdf)) achieves deadlock-freedom by construction — programs are global interaction descriptions compiled to local implementations. This is a *stronger* guarantee than SPEC-002 (which detects violations rather than preventing them), but requires centralised compilation that conflicts with CBCL's decentralised gossip model. Choreographies are a possible future direction for dialect authors who control both endpoints.

**Contemporary work.** Plumbing (William Waites, Leith Document Company, 2026) independently applies session types to LLM agent coordination, compiling them to barrier chains. We studied Plumbing's protocol documentation and found the convergence confirmatory — both systems arrive at the same primitives from the same theory. The engineering is different: Plumbing compiles to barrier chains for concurrent pipeline execution with linearity enforcement; we verify causal dependency graphs over message-passing with no ordering requirement.

**Event structure semantics for sessions.** Castellani, Dezani-Ciancaglini & Giannini (2024, [*Event Structure Semantics for Multiparty Sessions*](https://arxiv.org/abs/2201.00221)) interpret multiparty session types as flow event structures, which represent causality and concurrency explicitly rather than as sequential state machine transitions. This is the closest theoretical near-miss to SPEC-002's approach — it validates the direction of modelling sessions as causal structures rather than automata. However, event structures are used for semantic analysis (proving type soundness), not for runtime verification, and the paper does not address monotonicity, coordination-freedom, or CRDTs. SPEC-002 takes the causal-structure intuition and makes it operational: the causal graph is the message store itself, and verification is a monotone predicate on it.

**Merkle-CRDTs.** Sanjuan, Poyhtari, Teixeira & Psaras (2020, [*Merkle-CRDTs: Merkle-DAGs meet CRDTs*](https://research.protocol.ai/publications/merkle-crdts-merkle-dags-meet-crdts/psaras2020.pdf)) combine Merkle-DAGs with CRDTs, embedding causal ordering in content-addressed hash links. They note that "Merkle-Clocks already embed ordering and causality information which would otherwise need to travel embedded in the CRDT objects." This is the closest architectural precedent to SPEC-002's message store design — content-addressed, append-only, with causality embedded in hash pointers. The paper addresses data replication convergence, not protocol conformance checking. SPEC-002 applies the same architecture to a different problem: the Merkle DAG is not a replicated data store but a communication trace, and the monotone predicates verify protocol conformance rather than data convergence.

**Lattice-based determinism.** Kuper (2015, [*Lattice-Based Data Structures for Deterministic Parallel and Distributed Programming*](https://users.soe.ucsc.edu/~lkuper/papers/lindsey-kuper-dissertation.pdf), PhD dissertation, Indiana University) introduces LVars — lattice-based data structures with monotonic writes and threshold reads that guarantee deterministic parallelism. The algebraic machinery is close to SPEC-002's: data grows monotonically on a lattice, and observations (threshold reads / verification predicates) are monotone functions. Kuper applies this to deterministic parallel programming; SPEC-002 applies the same structure to protocol verification on an append-only message store.

**Coordination-free programming.** Meiklejohn & Van Roy (2015, [*Lasp: A Language for Distributed, Coordination-Free Programming*](https://dl.acm.org/doi/10.1145/2790449.2790525), PPDP 2015) build a programming model on lattice-typed CRDTs with monotonic operations, achieving coordination-freedom by construction. Lasp provides the programming model that SPEC-002's architecture resembles — monotonic operations on lattice-structured distributed state — but has no concept of protocol types or session verification.

**Runtime monitoring of sessions (the DFA baseline).** Neykova, Bocchi & Yoshida (2017, *Monitoring Networks through Multiparty Session Types*, ICTAC) and Neykova & Yoshida (2014/2017, [*Multiparty Session Actors*](http://mrg.doc.ic.ac.uk/publications/multiparty-session-actors/msa.pdf), COORDINATION/LMCS) represent the state of the art in decentralised session type monitoring. Each endpoint gets a local monitor projected from the global type. These monitors are finite automata that advance through states on each message — decentralised but not coordination-free in the CALM sense. The set of valid next messages changes with each state transition, which is non-monotonic. SPEC-002 departs from this baseline by eliminating stateful monitors entirely: verification is a lookup + type comparison on immutable data, not a state machine transition. This is the specific technical contribution that enables coordination-freedom.

The Francalanza/Scalas line is the closest published prior work to SPEC-002's monitor design. Bartolo Burlò, Francalanza & Scalas (2021, [*On the Monitorability of Session Types, in Theory and Practice*](https://arxiv.org/abs/2105.06291), ECOOP) provide a monitorability theory for binary session types and a Scala toolkit, with three-valued accept/reject/inconclusive verdicts in the standard runtime-verification style. The monitor model assumes the conventional in-order point-to-point channel model — no CRDT-structured store, no lattice-homomorphism property, and the inconclusive verdict is the generic LTL₃ "no decision yet" rather than a lattice ⊥ stable under store growth. Rowicki, Francalanza & Scalas (2025, [*Correct Black-Box Monitors for Distributed Deadlock Detection*](https://arxiv.org/abs/2508.14851), OOPSLA2) extend this line to distributed monitors over message traces, sound + complete, Coq-mechanised — but the verdict is binary (deadlocked / not), the property is liveness rather than session safety, and there is no CRDT or lattice machinery. SPEC-002's contribution against this baseline is to make the monitor a lattice homomorphism from a content-addressed CRDT message store to a three-valued result lattice, recovering coordination-freedom by CALM.

**Three-valued runtime verification.** Bauer, Leucker & Schallhart (2011, *Runtime Verification for LTL and TLTL*, TOSEM) introduced the canonical three-valued LTL₃ semantics for runtime monitoring, with verdicts `⊤` / `⊥` / `?` for "satisfied" / "violated" / "no decision yet on the prefix observed so far." Bauer & Falcone subsequently extended this to decentralised three-valued monitors. SPEC-002's three-valued result is the *shape* introduced by this line; the contribution is wiring the result lattice to a CRDT message store such that the third value (`Unknown` / ⊥) is *stable in the lattice ordering* — it can only move upward to `Valid` or `Violation` as the store grows — rather than the LTL₃ "undecided on the current prefix" reading.

**Causal-history monitors.** Cano, Mezzina & Pérez (2017, [*Causally consistent reversible choreographies: a monitors-as-memories approach*](https://www.researchgate.net/publication/320362576_Causally_consistent_reversible_choreographies_a_monitors-as-memories_approach), FORTE) embed causal histories directly into multiparty session monitors to support reversibility. This is the closest published precedent for treating causality as a first-class part of the monitor state rather than as transport metadata. The mechanism is causal but not lattice-monotone, the monitor is not framed as a homomorphism, and there is no CRDT or coordination-freedom argument. SPEC-002 takes the causal-history idea, makes the history itself the lattice (the message-store G-Set), and lifts the monitor to a monotone predicate on it.

**LangSec and session protocols.** Tse (2017, [*A Framework for Validating Session Protocols*](http://spw17.langsec.org/papers/tse-validating-session-protocols.pdf), LangSec Workshop/IEEE SPW) is the only prior work at the intersection of language-theoretic security and session type validation. The paper presents a Haskell-embedded DSL for specifying protocol state machines and validating message sequences against them. Like Neykova/Yoshida, the approach is DFA-based — state machine checking, not monotonic predicate checking. SPEC-002 shares the LangSec commitment to treating protocol messages as a formal language but replaces the state machine recogniser with monotone causal verification.

### The novel combination

The individual threads above are well-established. What has not appeared in the literature is their combination for agent communication protocols. A systematic search of the literature reveals a **community gap**: CALM/CRDT researchers (Berkeley — Hellerstein, Alvaro, Conway; Indiana — Kuper; UCLouvain — Meiklejohn) work on data management and deterministic parallelism; session type researchers (Imperial/Oxford — Yoshida, Honda, Carbone; Edinburgh — Wadler, Gay) work on process calculi and type theory. Neither community has crossed into the other's domain. SPEC-002 sits precisely in this gap.

The specific novel combinations:

- **CALM + session monitoring**: protocol invariants expressed as causal dependencies are monotonic, therefore coordination-free. Session type theory provides the protocol primitives; CALM (Ameloot 2011, restated by Hellerstein's *Coordination Criterion* in 2026) provides the coordination-freedom guarantee. No prior work connects these — Hellerstein's CALM line (2019, 2026) does not mention session types or session monitoring; Yoshida's monitoring work (2017) and the Francalanza/Scalas monitorability line (2021, 2025) do not mention monotonicity or coordination-freedom of the checking mechanism. The Coordination Criterion is the spec-level theorem; SPEC-002 is the first runtime monitor designed as a direct instantiation of it.
- **CRDTs + protocol verification**: the message store is a G-Set CRDT; protocol verification is a monotone predicate on the CRDT state. The verification converges without coordination because the underlying data structure does. Merkle-CRDTs (Sanjuan et al. 2020) provide the closest architectural precedent but apply the structure to data replication, not protocol conformance.
- **I-confluence + agent communication**: Bailis's invariant confluence criterion, originally for database integrity constraints, applies directly to protocol step constraints — "pause-ack must be caused by pause" is I-confluent. All prior I-confluence work (Bailis 2015, Whittaker & Hellerstein 2019) is restricted to database invariants.
- **Explicit causality + LangSec**: rather than relying on transport-level causal ordering (vector clocks, causal broadcast), each message carries its own causal reference as a keyword parameter within CBCL's DCFL grammar. The causal structure is self-describing and parseable by the same deterministic pushdown automaton that handles ordinary messages. Tse (2017) is the only prior LangSec + session protocol work, and uses DFA-based checking.
- **Causal structures over state machines for runtime verification**: Castellani et al. (2024) validate the theoretical direction — sessions modelled as causal event structures rather than sequential automata — but apply it to semantic analysis, not runtime verification. Cano/Mezzina/Pérez (2017) embed causal histories in monitors for reversible choreographies, but without lattice machinery or coordination-freedom claims. SPEC-002 makes this operational: the causal graph is the message store, verification is a monotone predicate, and the CALM theorem guarantees coordination-freedom.
- **Three-valued verdict + monotone result lattice**: Bauer/Leucker/Schallhart 2011 (LTL₃) and Bartolo Burlò/Francalanza/Scalas 2021 use three-valued verdicts where the third value means "no decision yet on the prefix observed so far." SPEC-002 reuses the three-valued shape but lifts the third value to a lattice ⊥ that is *stable under store growth* — a verdict can only move upward as the message store grows, never sideways or backward. This is what enables out-of-order delivery to be handled without false positives, and what distinguishes SPEC-002's verdict semantics from generic RV-LTL.

### Scope

This specification covers two orthogonal dimensions of structural verification:

**Protocols** (causal structure — which message types may follow which):
- Causal dependency declarations in CBCL S-expressions
- Predecessor validation on received messages
- Coordination-free verification (CALM-monotonic)

**Shapes** (message structure — what parameters a message must carry):
- Shape constraint grammar in CBCL S-expressions
- VPL tree-pattern checking on expanded messages
- Type constraints on parameter values
- Composition via VPL intersection

**Shared infrastructure:**
- Integration with the existing R1–R4 verification pipeline (as R5)
- DCFL preservation argument
- Monotonicity argument (CALM)

This specification does **not** cover:
- Counted sequences ("exactly N rounds then close") — non-monotonic by definition (aggregation); requires coordination per CALM
- Session delegation (passing channel endpoints as messages) — future work
- Value predicates in shape constraints (e.g., `price > 0`) — requires arithmetic, outside DCFL
- Multiparty global types — binary causal links only in this version

Note: fan-in (merge/join via `(all ...)`) IS covered by this specification. Fan-in verification is monotonic — a conjunction of positive existence checks on a grow-only store — and does not require coordination (ADR-007).

### Key Departure from SPEC-001

SPEC-001 encoded protocols as **state machines** (DFA). The current state determined what messages were valid next. This was non-monotonic: state changes, validity changes. ADR-004 acknowledged the ordering problem and deferred Lamport clocks.

SPEC-002 encodes protocols as **causal dependency declarations**. Each message carries a `:caused-by` reference to the message it responds to. The protocol declares which causal links are valid. Each check is: "does the referenced message exist, and is its type a valid predecessor?" This is monotonic: messages are immutable, causal links are immutable, the check is a positive assertion about immutable facts.

| | SPEC-001 (DFA) | SPEC-002 (Causal) |
|---|---|---|
| Protocol encoding | State machine (DFA transition table) | Dependency graph (predecessor declarations) |
| Mutable state | `protocol_states: BTreeMap<String, usize>` per thread | None — stateless verification |
| Message ordering | Required (ADR-004 — arrival order or Lamport clocks) | Not required — causality is in the message |
| Monotonic (CALM) | No | Yes |
| Coordination-free | No | Yes |
| Counted sequences | Yes (DFA can count) | No (counting is aggregation, non-monotonic) |
| Fan-in (merge/join) | No (DFA is single-state) | Yes — `(all ...)` with list-valued `:caused-by` |
| Unreliable transport | Problematic (reordering causes false violations) | Works — each message is self-describing |
| Expressiveness | Regular languages | Merkle DAGs with fan-out and fan-in |

---

## User Profiles

### User: Dialect Author

**Role:** Developer or agent designing a domain-specific dialect for CBCL.

**Goals:** Define not just what messages exist (performatives) but what causal relationships between messages are valid. Prevent consumers from sending messages without the required causal predecessors. Communicate protocol expectations as machine-checkable contracts.

**Constraints:** Must express protocols within S-expression syntax. Protocol declarations must be transmittable via `(meta (teach ...))`. Must not require understanding of linear logic or category theory.

**Daily workflow:** Defines a dialect with `extend` clauses, adds a `protocol` clause declaring causal dependencies between performatives, optionally adds `shape` clauses for structural requirements, tests with `:examples`, publishes via gossip.

### User: Dialect Consumer (Agent)

**Role:** An agent receiving a dialect definition via `(meta (teach ...))` from an untrusted peer.

**Goals:** Verify that the dialect is safe (R1–R4) and that the protocol and shape declarations are well-formed (R5). Install the dialect. Verify causal dependencies on received messages. Reject messages with invalid causal predecessors. Produce well-typed errors on violation.

**Constraints:** Verification must be stateless and coordination-free. Protocol checking must not require message ordering or mutable per-thread state. Must handle missing `:caused-by` parameters gracefully (skip causal verification or reject per policy).

---

## Happy Paths

### Happy Path: Dialect Author Defines a Causal Protocol

**Preconditions:** Author has a working dialect with `extend` clauses.

**Steps:**
1. Author adds a `(protocol ...)` clause declaring causal dependencies → Parser accepts.
2. Author runs `cbcl-cli verify` → CLI reports R1–R5 pass, prints the dependency graph.
3. Author adds `:examples` with `:caused-by` references → Examples verified against protocol.
4. Author transmits via `(meta (teach ...))` → Receiving agent parses, verifies R1–R5, installs.

**Postconditions:** Dialect installed with causal dependency declarations.

**Failure modes:**
- Protocol references undefined performative → R5 rejects.
- Circular causal dependency (`a :after a`) → R5 rejects.
- Step with no `:after` clause and not marked as protocol start → R5 rejects.

### Happy Path: Agent Verifies Causal Dependency at Runtime

**Preconditions:** Dialect with protocol installed. Message received with `:caused-by` reference.

**Steps:**
1. Agent receives message with `:caused-by msg-042` → Looks up `msg-042` in message store.
2. Agent checks: is `msg-042`'s performative a valid predecessor for this message's performative per the protocol? → Yes.
3. Message proceeds to shape checking and delivery.

**Postconditions:** Causal link verified. No state mutated.

**Failure modes:**
- Referenced message `msg-042` not found → `(error @sender "causal-violation" :detail "unknown-predecessor" :caused-by "msg-042")`.
- Referenced message has wrong performative type → `(error @sender "causal-violation" :detail "invalid-predecessor" :caused-by "msg-042" :expected "pause" :found "get-memory")`.
- Message has no `:caused-by` parameter and dialect protocol requires it → Agent policy: reject or skip causal check.

---

## Requirements

### REQ-200: Causal Protocol Declarations

The system SHALL support `(protocol ...)` clauses in dialect definitions that declare the valid causal dependencies between performatives. A protocol declaration consists of one or more `then` forms, each declaring a causal chain:

```scheme
;; Compaction — pure sequence
(protocol
  (then begin pause pause-ack get-memory
    memory-dump set-memory set-memory-ack resume))

;; Document operations — choice + concurrent fan-out
(protocol
  (then begin (any read write close))
  (then read content)
  (then write ack)
  (then (any content ack) (any read write close)))

;; Request-response loop
(protocol
  (then (any begin response) request response))

;; Scatter-gather — concurrent fan-out then fan-in (merge)
(protocol
  (then begin (all search-a search-b search-c))
  (then search-a result-a)
  (then search-b result-b)
  (then search-c result-c)
  (then (all result-a result-b result-c) merge-results))

;; Two-phase commit — coordinator waits for all votes
(protocol
  (then begin prepare)
  (then prepare (any vote-yes vote-no))
  (then (all vote-yes vote-yes) commit)
  (then vote-no abort))
```

The `then` form is variadic. Arguments are processed pairwise left to right: each argument's performatives may follow the previous argument's performatives. A bare symbol is a single step. An `(any ...)` form denotes **alternatives** — disjunction at that step. An `(all ...)` form denotes **conjunction** — all listed items participate. The special symbol `begin` denotes the protocol start — no prior message required.

The semantics of `(any ...)` and `(all ...)` differ by position:

| Position | `(any ...)` | `(all ...)` |
|---|---|---|
| **Left** (predecessor) | Disjunction: predecessor may be any one of these types. Single `:caused-by` hash. | Conjunction: ALL listed predecessor types must be present. List-valued `:caused-by`. Fan-in. |
| **Right** (successor) | Choice: one of these may follow. Edges to all listed types. | Concurrent: all of these proceed. Edges to all listed types. Sender SHOULD emit all. |

On the **left** (predecessor) side, both forms are monotonically enforceable:
- `(any a b)` — "is the predecessor's type in {a, b}?" — set membership on immutable data.
- `(all a b)` — "are predecessors of types a AND b present?" — conjunction of existence checks on a grow-only store.

On the **right** (successor) side, both forms generate the same edges in the dependency graph. The difference is **intent**: `(any ...)` declares exclusive choice (the sender picks one), `(all ...)` declares concurrent fan-out (the sender emits all). The verifier cannot enforce exclusivity — "at most one successor" requires checking that no sibling response exists, which is non-monotonic (the arrival of one response invalidates another). Exclusivity is a sender obligation, not a verifier-enforceable property. The distinction is still valuable: it communicates the dialect author's design intent and enables static analysis tooling to flag violations.

For the Compaction example, `(then begin pause pause-ack ...)` desugars to the edges: `begin→pause`, `pause→pause-ack`, `pause-ack→get-memory`, etc. For the document operations example, `(then begin (any read write close))` desugars to: `begin→read`, `begin→write`, `begin→close` — the sender chooses one. When both sides use `(any ...)`, the Cartesian product applies: `(then (any content ack) (any read write close))` desugars to six edges.

For the scatter-gather example, `(then begin (all search-a search-b search-c))` means: after `begin`, the sender SHOULD emit all three search messages (concurrent fan-out). The right-side `(all ...)` declares intent; each individual search message's `:caused-by` still points to `begin`. On the left side, `(then (all result-a result-b result-c) merge-results)` means: `merge-results` is valid only when its `:caused-by` parameter lists hashes of all three result messages. The verifier checks that all three hashes resolve to messages of the declared types — a conjunction of monotone predicates on the append-only store.

**Rationale:** This replaces SPEC-001's DFA state machine with a dependency graph. The graph is static (declared at installation, never mutated). Each runtime check is a lookup + type comparison — monotonic, stateless, coordination-free. By the CALM theorem, this formulation has a consistent coordination-free distributed implementation. Fan-in via `(all ...)` is monotonic because a conjunction of positive existence checks on a grow-only store can only transition from false to true, never the reverse (ADR-007).

verified-by: prose

Trace:
- TEST-200
- CON-200

### REQ-201: Causal Protocol S-Expression Grammar

The system SHALL parse causal protocol declarations from S-expression syntax. The grammar in ABNF (RFC 5234):

~~~abnf
; ================================================================
; Layer 4a: Causal protocol grammar (extension to Layer 3)
;
; Entered via (protocol ...) clause within a dialect definition.
; The "protocol" keyword dispatches deterministically in
; dialect-clause.
;
; Verification class: monotonic graph lookup.
; No state machine. No ordering requirement.
; DCFL preservation: protocol declarations are S-expressions
; parsed by the existing Layer 1 recogniser.
;
; Theoretical basis:
;   - Honda 1993 (session type primitives)
;   - CALM theorem (monotonic = coordination-free)
;   - Lamport 1978 (causal ordering via happened-before)
; ================================================================

; --- Dialect clause extension ---
;
;   dialect-clause =/ protocol-clause

protocol-clause  = "(" "protocol" 1*(WS then-decl) ")"

then-decl        = "(" "then" 2*(WS node-ref) ")"
                 ; Variadic. Pairwise left-to-right: each node-ref
                 ; may follow the previous. When either side is a
                 ; list, the Cartesian product of edges applies.
                 ; Minimum 2 arguments.

node-ref         = performative-ref
                 / "(" "any" 2*(WS performative-ref) ")"
                 / "(" "all" 2*(WS performative-ref) ")"
                 ; Atom = single step in the chain.
                 ; (any ...) = alternatives (disjunction).
                 ;   Left side: predecessor may be any one of
                 ;   these types. Right side: sender chooses one.
                 ; (all ...) = conjunction.
                 ;   Left side: all listed predecessor types must
                 ;   be present (fan-in). Right side: all proceed
                 ;   concurrently (fan-out). Sender SHOULD emit all.
                 ; Both require minimum 2 arguments.

performative-ref = "begin" / symbol
                 ; "begin" = protocol start (no prior message).
                 ; symbol = performative name.
                 ; MUST match an extend clause in this dialect
                 ; or an installed ancestor (REQ-206).
~~~

**Dispatch determinism.** `protocol` is a symbol, distinct from all other dialect-clause head tokens. Within a `protocol-clause`, `then` is the only valid head. Within a `then-decl`, each argument is either a bare symbol, `(any ...)` (disjunction), or `(all ...)` (conjunction). The head keyword (`any` or `all`) deterministically dispatches the interpretation. No bare lists without a head keyword — the head is always required. LL(1) at every level.

verified-by: property

Trace:
- TEST-201
- CON-201

### REQ-202: The `:caused-by` Message Parameter

Messages participating in a causal protocol SHALL carry a `:caused-by` keyword parameter referencing one or more causal predecessors. The value is either:

- The string `"begin"` (protocol start — no prior message required).
- A single content hash of the predecessor message's canonical serialisation (RFC 9804).
- A list of content hashes (for merge/join messages with multiple causal predecessors).

```scheme
;; Single predecessor
(lang compaction
  (pause "context full" :caused-by "begin"))

(lang compaction
  (pause-ack :caused-by "sha256:7d3e...a1f0"))

;; Multiple predecessors (fan-in / merge)
(lang search
  (merge-results :caused-by ("sha256:a1b2...c3d4"
                              "sha256:e5f6...7890"
                              "sha256:1a2b...3c4d")))
```

A message's identity is the SHA-256 hash of its canonical serialisation. This is content addressing: the identifier is derived from the message content, not assigned by any party. Both sender and receiver compute the same hash independently. No ID authority, no coordination, no possibility of fabrication (would require a hash collision).

The result is a **Merkle DAG** of messages: each `:caused-by` is one or more hash pointers to predecessors. The causal graph is cryptographically tamper-evident. Altering any message invalidates all downstream hash references. A third party (e.g., an escrow service) can independently verify the entire interaction history from the messages alone, without having participated in the conversation.

`:caused-by` is syntactically a keyword parameter, already legal in CBCL's grammar (Layer 2). No grammar extension is needed. A single hash is an atom; a list of hashes is a parenthesised list — both are valid Layer 1 forms. The parameter is extracted by the protocol checker alongside `:thread`, `:in-reply-to`, and `:sender`. Canonical serialisation for hashing is already implemented in `cbcl-rs` (`canonical.rs`, used for dialect signature verification via RFC 9804).

Content-addressed `:caused-by` is a SHOULD. An implementation MAY use opaque identifiers (e.g., UUIDs) at the cost of requiring additional trust for third-party verification. Content hashing makes verification fully trustless.

**Fan-in semantics.** When `:caused-by` is a list of hashes, the message is a **merge message** — it has multiple causal predecessors. The protocol declaration determines which predecessor types are required via `(all ...)` node references (REQ-200). The verifier checks that each hash in the list resolves to a message in the store and that the set of predecessor performative types satisfies the conjunction declared in the protocol. See REQ-203 for the verification procedure.

**Canonical ordering of `:caused-by` lists.** When `:caused-by` is a list of hashes (fan-in), the hashes SHALL be sorted in lexicographic (byte-wise ascending) order in the canonical serialisation used for content hashing. This ensures that two agents constructing the same logical merge message — referencing the same set of predecessors — produce the same content hash regardless of the order in which they observed the predecessors. Without canonical ordering, the `:caused-by` list order would affect the message hash, breaking the identity property: same logical message → same hash. The sort is applied during canonical serialisation (before hashing), not necessarily in the wire format — implementations MAY transmit hashes in any order but MUST sort before computing the content hash.

**Rationale:** Explicit causal references make protocol structure self-describing. Each message declares its own position in the causal graph. Content addressing makes the graph tamper-evident and independently verifiable. This eliminates the need for message ordering, Lamport clocks, mutable per-thread state, or a trusted ID authority. The causal graph is a grow-only Merkle DAG of immutable (hash, performative, caused-by-hash) triples, a content-addressed CRDT. Fan-in is monotonic: a conjunction of positive existence checks on a grow-only store can only transition from false to true (ADR-007).

verified-by: example

Trace:
- TEST-202

### REQ-203: Causal Verification (Stateless)

The system SHALL verify causal dependencies on each incoming message without mutable state. The verification procedure:

1. Extract `:caused-by` from the incoming message.
2. If `:caused-by` is `"begin"`, check that the message's performative has `begin` as a valid predecessor in the protocol declaration.
3. If `:caused-by` is a single message ID (atom), look up the referenced message in the agent's message store (conversation thread history). Check that:
   a. The referenced message exists.
   b. The referenced message's performative is a valid predecessor for the incoming message's performative, per the protocol declaration (disjunctive predecessor set).
4. If `:caused-by` is a list of message IDs (fan-in / merge), verify conjunctive predecessor requirements:
   a. Look up each referenced message in the message store. All must exist.
   b. Collect the multiset of predecessor performative types.
   c. Check that the protocol declaration has an `(all ...)` predecessor for the incoming message's performative.
   d. Check that every performative type required by the `(all ...)` declaration is present in the collected multiset. The `(all ...)` declaration lists the required types; each required type must appear at least once.
   e. Check that no hash in the list references a performative type that is NOT in the `(all ...)` declaration (no extraneous predecessors).
5. If any check fails, reject with a well-typed error (see failure modes in Happy Path).
6. If the dialect has no `(protocol ...)` clause, skip causal verification.
7. If the message has no `:caused-by` parameter and the dialect has a protocol, the agent MAY reject or skip per policy.

This procedure is **stateless**: it reads the protocol declaration (static, installed at dialect installation) and the message store (append-only, grow-only). It writes nothing. It depends on no ordering. It can be run at any time, in any order, by any agent, and produce the same result.

**Monotonicity of fan-in verification.** Step 4 is a conjunction of positive existence checks on the append-only store. Each sub-check ("does hash H resolve to a message of type T?") is individually monotone. Their conjunction is monotone: once all predecessors are present with correct types, adding new messages to the store cannot invalidate any of the sub-checks. By CALM, fan-in verification is coordination-free.

**Rationale:** Statelessness is the key property. SPEC-001's DFA required `protocol_states: BTreeMap<String, usize>` — mutable state per thread, updated on each message. This specification requires only a read of the message store, which is append-only. By CALM, this is coordination-free. Fan-in adds O(k) lookups per merge message (where k = number of predecessors) but does not change the coordination-freedom guarantee.

verified-by: example

Trace:
- TEST-203
- CON-202

### REQ-204: Protocol Acyclicity

The system SHALL reject protocol declarations containing cycles in the dependency graph. A cycle means performative A lists B as a predecessor, and B lists A as a predecessor (directly or transitively).

`begin` is not a performative and cannot be a dependency target — it is a source only.

**Rationale:** Cycles in the causal graph would allow circular justification — message A valid because of B, B valid because of A. This is well-founded induction: every causal chain must terminate at `begin`. Acyclicity is checked at installation (R5) using the same DFS cycle detection as R1's mutual recursion check.

Note: loops (repeated request-response) are NOT cycles in the concrete message graph. A request-response loop is declared as `(then (begin response) request response)`. The dependency graph has an edge `response→request`, which looks circular at the *schema* level. But at runtime, each concrete message has a unique ID: `begin → request-1 → response-1 → request-2 → response-2 → ...` is acyclic. The acyclicity check (REQ-204) operates on the *schema* graph and must permit cycles that represent loops — see REQ-204 for the distinction.

verified-by: lean

Mechanised in `lean-cbcl/LeanCbcl/R5.lean` as `check_acyclicity_iff_no_cycle` (full iff). Soundness is `checkAcyclicity_sound`; completeness is `checkAcyclicity_complete`, by strong induction on the DFS recursion depth — in cycle-free graphs every visiting-set element is a graph key with a back-edge to the current node, so by acyclicity all visiting elements are distinct keys, hence `|visiting| ≤ |stepNames|` and fuel `|stepNames|² + 1 ≥ |stepNames| + 1` is more than sufficient.

Trace:
- TEST-204

### REQ-205: Protocol Reachability

The system SHALL reject protocol declarations where any step is unreachable from `begin`. Every performative declared in a `step` must be reachable by following predecessor links back to `begin`.

**Rationale:** An unreachable step can never be validly invoked — its predecessors are not in the protocol, so no message can satisfy its `:after` clause. This catches dead code in protocol declarations.

verified-by: lean

Mechanised in `lean-cbcl/LeanCbcl/R5.lean` as `check_reachability_iff_all_reachable` (full iff). Soundness is `checkReachability_sound`; completeness is `checkReachability_complete`, via path extraction: any `Reachable` proof is converted to an explicit `ReachableViaPath`, simplified to a `Nodup` simple path of length ≤ `|stepNames|`, then `dfsReaches` is shown to follow the simple path step-by-step at fuel `|stepNames|² + 1`.

Trace:
- TEST-205

### REQ-206: Well-Formedness — Performative Definedness

The system SHALL reject a protocol declaration that references a performative name not defined by an `extend` clause in this dialect or an installed ancestor dialect.

The special token `begin` is always valid and does not need an `extend` clause.

verified-by: lean

Mechanised in `lean-cbcl/LeanCbcl/R5.lean` as `check_performative_definedness_iff_all_defined` (full iff).

Trace:
- TEST-206

### REQ-207: Well-Formedness — Step Uniqueness

The system SHALL reject a protocol declaration containing duplicate `step` declarations for the same performative.

**Rationale:** Duplicate steps create ambiguous predecessor sets. Each performative has exactly one set of valid predecessors.

verified-by: lean

Mechanised in `lean-cbcl/LeanCbcl/R5.lean` as `check_step_uniqueness_iff_no_duplicates` (full iff).

Trace:
- TEST-207

### REQ-208: R5 Verification at Installation

The system SHALL verify the following conditions when installing a dialect with a `(protocol ...)` clause, as a new constraint R5:

1. Parse the protocol clause into a dependency graph (REQ-201).
2. Check acyclicity (REQ-204).
3. Check reachability from `begin` (REQ-205).
4. Check performative definedness (REQ-206).
5. Check step uniqueness (REQ-207).

If any check fails, reject with `DialectInstallError::R5Violation`. If the dialect has no `(protocol ...)` clause, R5 passes trivially.

R5 verification for protocols runs in O(|P|²) time where |P| is the number of steps, dominated by the DFS for acyclicity and reachability. This is the same complexity class as R1 verification.

For shape constraints, R5 additionally verifies shape well-formedness (REQ-222).

verified-by: example

Trace:
- TEST-208

### REQ-209: DCFL Preservation Under Causal Protocols

The system SHALL preserve DCFL membership when installing a dialect with a causal protocol declaration. The argument:

1. **Parsing.** The `(protocol ...)` clause is an S-expression parsed by the existing DCFL recogniser. The `protocol` keyword is a deterministic dispatch token.
2. **Verification.** Causal verification is a lookup in the message store (hash map access) + a membership check against the predecessor set (finite set lookup). Neither operation extends the grammar or increases the parser's computational power.
3. **No grammar extension.** Unlike SPEC-001's DFA (which introduced a recogniser for a regular language of traces), causal verification introduces no recogniser at all. It is a predicate on pairs of messages, not a language membership check.

DCFL preservation is trivially maintained because the protocol mechanism adds no new parsing capability — it is a post-parse, post-expansion verification predicate on immutable data.

verified-by: lean (placeholder)

Mechanised in `lean-cbcl/LeanCbcl/DCFLPreservation.lean` as `dcfl_preserved_under_protocol` (the `(protocol …)` clause inhabits the existing `IsSExpr` DCFL grammar) and `protocol_dispatch_specifies` (the wired `protocol` branch in `applyKeywordClause` has pinned operational semantics: a single string-like value updates the `protocol` field). The DCFL closure proof is short by design: causal verification is a post-parse, post-expansion predicate over already-built `SExpr` trees (VPL ⊂ DCFL), so closure under `(protocol …)` reduces to `allSExpr_isSExpr _` — the existing recogniser already accepts every `SExpr`, including this clause shape. The named theorem is therefore a `lean (placeholder)` per the convention established by SPEC-003 REQ-308; the substantive content lives in the companion `protocol_dispatch_specifies` lemma. A longer DCFL-preservation proof would only be needed if `protocol` extended the parser; it does not.

Trace:
- TEST-209

### REQ-210: Dialect Transmission of Structural Contracts

The system SHALL include protocol and shape declarations in `(meta (teach ...))` messages. Both are S-expression clauses within the dialect definition, transmitted and verified using existing infrastructure.

verified-by: example

Trace:
- TEST-210

### REQ-211: Monotonicity Guarantee

Every verification operation introduced by this specification SHALL be monotonic in the sense of the CALM theorem: adding new messages to the message store SHALL NOT invalidate any previously valid causal link.

Formally: if `causal_check(msg, store) = Valid` then `causal_check(msg, store ∪ {new_msg}) = Valid` for all `new_msg`. Symmetrically, if `causal_check(msg, store) = Violation` then `causal_check(msg, store ∪ {new_msg}) = Violation` for all `new_msg`. Both `Valid` and `Violation` are stable (permanent) under store growth. Only `Unknown` (predecessor not yet in store) may change as the store grows.

This holds for both single-predecessor and multi-predecessor (fan-in) verification:

- **Single predecessor:** `verify(msg, store) = Valid` requires predecessor hash H to exist in the store with type T. Adding messages to the store cannot remove H or change its type. `Valid` is stable. `Violation` is stable by the same argument.
- **Multi-predecessor (fan-in):** `verify(msg, store) = Valid` requires ALL predecessor hashes H₁...Hₖ to exist in the store with types T₁...Tₖ. Each sub-check is individually monotone (same argument as single). Meet of monotone functions is monotone. `Valid` is stable.

**Algebraic foundation.** The monotonicity guarantee is proved structurally — not by case analysis — in SPEC-003 (Verification Lattice). The message store is a join-semilattice (G-Set CRDT), the verification result is a flat poset with bottom `Unknown`, and the verification function is a monotone map between them (SPEC-003 REQ-304). Compositional closure (meet for `(all ...)`, join for `(any ...)`) preserves monotonicity automatically. See SPEC-003 for the full algebraic treatment and Lean 4 proof targets.

**Rationale:** This is the property that makes the system coordination-free. SPEC-001's DFA violated this: receiving message X could advance the DFA state, causing a previously valid message Y to become invalid in the new state. Causal verification does not have this problem — it checks a static predicate on immutable data. Fan-in adds conjunctive checks but preserves monotonicity because meet over monotone functions is monotone.

verified-by: property

Trace:
- TEST-211

### REQ-212: Thread Topology — Merkle DAG, Verification Tiers, and Causal Closure

Each thread is a **Merkle DAG**: a directed acyclic graph where nodes are messages and edges are `:caused-by` hash pointers (REQ-202). The topology is determined by the interaction pattern:

| Pattern | Fan-out | Fan-in | Topology |
|---|---|---|---|
| Pure sequence (e.g., compaction) | No | No | Linked list |
| Concurrent replies | Yes | No | Tree |
| Scatter-gather, barriers | Yes | Yes | DAG |

The DAG is not a separate data structure — the messages themselves ARE the DAG. Each message's `:caused-by` field is its adjacency list (back-pointers to parents). The message store is the DAG.

**Definitions.**

- A **root message** is a message whose `:caused-by` value is `"begin"`. Every thread has at least one root.
- A **leaf message** is a message that is not referenced by any other message's `:caused-by` parameter. Leaves are the open ends of the conversation — the frontier from which new messages may extend.
- The **frontier** of a thread is the set of all leaf messages. The frontier represents the current actionable state of the interaction.
- The **causal closure** of a message M is the set of all messages reachable by transitively following `:caused-by` links from M back to root(s). This is the minimal subset of the thread needed to fully verify M's causal history.

**Fan-out (branching).** Multiple messages MAY reference the same predecessor via `:caused-by`. This produces branching — e.g., two agents independently reply to the same message. Each branch is independently valid. Causal verification (REQ-203) checks each message's predecessor individually; fan-out introduces no new verification burden.

```scheme
;; Agent A and Agent B both reply to the same pause message:
(lang compaction (pause-ack :caused-by "sha256:7d3e...a1f0" :sender "agent-a"))
(lang compaction (pause-ack :caused-by "sha256:7d3e...a1f0" :sender "agent-b"))
```

**Fan-in (merging).** `:caused-by` accepts a list of hashes, enabling merge messages with multiple causal predecessors. Fan-in is what makes the thread topology a DAG rather than a tree — a message with two or more parents cannot be represented as a tree or linked list. Fan-in requires an `(all ...)` declaration in the protocol (REQ-200) and conjunctive verification of all listed predecessors (REQ-203). Fan-in verification is monotonic: a conjunction of positive existence checks on a grow-only store (ADR-007).

```scheme
;; Fan-in: merge-results caused by three independent results
(lang search
  (merge-results :caused-by ("sha256:a1b2...c3d4"
                              "sha256:e5f6...7890"
                              "sha256:1a2b...3c4d")))
```

**Thread-scoped causality.** The `:caused-by` hash MUST reference a message within the same `:thread`. Cross-thread causal references are invalid — a verifier SHALL reject a message whose `:caused-by` hash resolves to a message in a different thread. Threads are causally independent partitions of the message store.

#### Verification Tiers

Not all participants need all messages. The monotonicity guarantee (REQ-211) means that once a causal link is verified, it stays verified as the store grows. This enables three verification tiers:

**Tier 1: Incremental (runtime).** To verify an incoming message M, a participant needs only M's direct predecessors — the messages whose hashes appear in M's `:caused-by`. Those predecessors were already verified when they arrived. This is O(1) for single-predecessor messages and O(k) for fan-in with k predecessors. This is the common case for active participants.

**Tier 2: Partial (causal closure).** To verify a message M from scratch (e.g., joining a thread mid-conversation), a participant needs M's **causal closure** — all messages reachable by following `:caused-by` links back to root(s). This is a DAG traversal. The participant does NOT need messages on unrelated branches. For a linked-list topology, the causal closure is the entire prefix. For a DAG, it may be a strict subset of the thread.

**Tier 3: Full (third-party audit).** To verify an entire thread (e.g., escrow, dispute resolution), a verifier needs all messages. The procedure:

1. **Recompute identities.** For each message, compute SHA-256 of the canonical serialisation. The computed hash IS the message identity.
2. **Reconstruct the DAG.** For each message, follow `:caused-by` to its predecessor(s). Single-predecessor messages form edges; multi-predecessor messages form merge nodes.
3. **Verify causal validity.** For each message, check that its predecessor(s) are valid per the protocol declaration (REQ-203). For merge messages with list-valued `:caused-by`, verify the conjunction of required predecessor types.
4. **Verify completeness.** The DAG is complete if every `:caused-by` hash resolves to a message in the set. Any unresolvable hash indicates a missing message — the thread is incomplete.
5. **Identify the frontier.** Leaf messages (unreferenced by any `:caused-by`) are the open ends. The frontier tells the verifier where the interaction stands.
6. **Detect tampering.** Any alteration to a message changes its hash, breaking all downstream `:caused-by` references. Tampering is structurally detectable without signatures — the DAG becomes internally inconsistent.

No trust in any participant is required. The verifier needs only the messages themselves and the dialect definition (which contains the protocol declaration). Both are self-describing CBCL S-expressions.

#### DAG-Aware Operations

The `(all ...)` construct requires DAG-aware operations that go beyond linked-list traversal:

- **Acyclicity verification** at the message level — a message cannot be its own ancestor. For single-predecessor messages this is trivially guaranteed by content addressing (a message's hash depends on its content, so it cannot reference itself). For fan-in, the verifier must additionally ensure that the `:caused-by` list does not introduce a cycle through the merge structure.
- **Completeness checking** — all hashes in `:caused-by` lists must resolve to messages in the store. For fan-in, ALL listed hashes must resolve, not just one.
- **Causal closure computation** — given a message M, compute the set of all ancestors by DAG traversal (BFS/DFS following `:caused-by` links). This is a graph operation, not a list walk. Required for Tier 2 verification and for constructing the minimal message subset needed to verify M.

**Rationale:** The message store is a content-addressed Merkle DAG partitioned by thread. The topology is emergent — determined by the interaction pattern, not imposed by the data structure. Sequential protocols produce linked lists. Concurrent protocols produce trees. Protocols with `(all ...)` barriers produce DAGs. The DAG is the general case; lists and trees are special cases. Verification is tiered: active participants verify incrementally (Tier 1), late joiners verify their causal closure (Tier 2), auditors verify everything (Tier 3). All three tiers are monotonic on the append-only store.

verified-by: example

Trace:
- TEST-212

---

### REQ-220: Structural Shape Constraints

The system SHALL support `(shape ...)` clauses in dialect definitions that declare the required structure of expanded messages. Shape constraints specify which keyword parameters must or may be present, their expected atom types, and maximum nesting depth.

Shape constraints are the second dimension of structural contracts, orthogonal to protocols. Protocols constrain causal structure (which message follows which). Shapes constrain individual message structure (what parameters a message carries).

Shape constraints are monotonic: checking "does parameter `:package` of type `string` exist in this S-expression" is a positive assertion on immutable data.

verified-by: property

Trace:
- TEST-220
- CON-203

### REQ-221: Shape Constraint S-Expression Grammar

The system SHALL parse shape constraints from S-expression syntax:

```scheme
(shape track-shipment
  (require :package string)
  (require :route string)
  (optional :priority string "normal")
  (max-depth 4))

(shape propose-step
  (require :action symbol)
  (require :params list
    (require :target string)
    (optional :deadline string))
  (max-depth 6))
```

The grammar in ABNF:

~~~abnf
; ================================================================
; Layer 4b: Shape constraint grammar (extension to Layer 3)
;
; Entered via (shape ...) clause within a dialect definition.
;
; Verification class: VPL (visibly pushdown language).
; VPL ⊂ DCFL. Monotonic (positive assertions on immutable tree).
;
; Theoretical basis: Alur & Madhusudan 2004 (VPL closure).
; ================================================================

; --- Dialect clause extension ---
;
;   dialect-clause =/ shape-clause

shape-clause     = "(" "shape" WS performative-name
                   1*(WS shape-rule) ")"

performative-name = symbol

shape-rule       = require-rule / optional-rule
                 / max-depth-rule

require-rule     = "(" "require" WS keyword
                   [WS type-constraint]
                   *(WS shape-rule) ")"

optional-rule    = "(" "optional" WS keyword
                   [WS type-constraint]
                   [WS default-value]
                   *(WS shape-rule) ")"

max-depth-rule   = "(" "max-depth" WS number ")"

type-constraint  = "string" / "number" / "bool"
                 / "symbol" / "keyword" / "list"

default-value    = s-expr
~~~

verified-by: property

Trace:
- TEST-221
- CON-203

### REQ-222: Shape Verification at Installation (R5)

The system SHALL verify each `(shape ...)` clause at installation:

1. Performative name matches an `extend` clause.
2. All keywords are valid CBCL keywords (start with `:`).
3. All type constraints are one of the six recognised types.
4. `max-depth` does not exceed the dialect's R2 bound.
5. No duplicate require/optional for the same keyword at the same depth.

verified-by: example

Trace:
- TEST-222

### REQ-223: Runtime Shape Checking

The system SHALL verify expanded messages against shape constraints after template expansion and before delivery. The check walks the expanded S-expression and verifies:
- All `require` parameters present at expected depth.
- Present parameters satisfy type constraints.
- Nesting depth within `max-depth`.
- Nested rules satisfied recursively.

Shape checking is monotonic: it is a positive assertion about the structure of an immutable S-expression.

verified-by: example

Trace:
- TEST-223
- CON-204

### REQ-224: Shape Composition via VPL Intersection

Multiple shape constraints on the same performative compose via conjunction. VPL closure under intersection guarantees the conjunction is still VPL ⊂ DCFL.

verified-by: prose

Trace:
- TEST-224

### REQ-225: DCFL Preservation Under Shape Constraints

Shape checking is a VPL tree-walking operation. VPL ⊂ DCFL. Shape constraints do not extend the grammar. DCFL preservation is maintained.

verified-by: lean (placeholder)

Mechanised in `lean-cbcl/LeanCbcl/DCFLPreservation.lean` as `dcfl_preserved_under_shape` (the `(shape …)` clause inhabits the existing `IsSExpr` DCFL grammar) and `shape_dispatch_currently_unwired` (the `shape` keyword is not yet wired into `applyKeywordClause` and routes to its catch-all error branch — the DCFL preservation argument does not depend on it being wired, only on `(shape …)` being a well-formed `SExpr`). The DCFL closure proof is short by design: shape checking is a VPL tree-walking operation on the parsed `SExpr` (VPL ⊂ DCFL), so closure under `(shape …)` reduces to `allSExpr_isSExpr _` — the existing recogniser already accepts every `SExpr`, including this clause shape. The named theorem is therefore a `lean (placeholder)` per the convention established by SPEC-003 REQ-308; the substantive content lives in the companion `shape_dispatch_currently_unwired` lemma (which will be replaced by a `shape_dispatch_specifies` analogue once `shape` is wired). A longer DCFL-preservation proof would only be needed if `shape` extended the grammar, which it does not. See REQ-209 for the same argument applied to causal protocols.

Trace:
- TEST-225

### REQ-230: Correct Blame

Every violation error produced by the structural contract system SHALL correctly identify the responsible party. Structural contracts involve three distinct parties:

1. **Dialect author** — defined the protocol and shape constraints (identified by Ed25519 signature on the dialect definition).
2. **Sending agent** — produced the message that violated a constraint (identified by `:sender` parameter or transport-level identity).
3. **Installing agent** — chose to install the dialect and is responsible for enforcing its contracts locally (the receiving agent itself).

Blame correctness requires that violations are attributed to the party whose action caused the violation, not merely the party closest to the failure:

| Violation | Blamed party | Rationale |
|---|---|---|
| Message fails shape constraint | Sending agent | Sender produced a message that does not conform to the dialect's declared shape. |
| Message fails causal check (invalid predecessor) | Sending agent | Sender referenced a predecessor that does not satisfy the protocol's dependency declaration. |
| Message fails causal check (unknown predecessor) | Sending agent | Sender referenced a message ID not present in the receiver's store. May also indicate network partition — blame is tentative. |
| Shape constraint is unsatisfiable (no valid message can match) | Dialect author | The dialect definition contains a contradictory shape. Detected at installation (R5) if witness/examples are present; otherwise at first runtime failure. |
| Protocol is malformed (unreachable steps, undefined performatives) | Dialect author | The dialect definition contains a broken protocol. Detected at installation (R5). |
| Agent installs dialect with known R5 violations | Installing agent | Agent chose to override or skip R5 verification. |

Violation errors SHALL carry sufficient information for a third party to independently verify blame:

```scheme
(error @sender "shape-violation"
  :dialect "logistics"
  :dialect-author "@consortium"
  :dialect-hash "sha256:abc1...def2"       ;; identifies exact dialect version
  :performative "track-shipment"
  :rule "require"
  :field ":route"
  :expected "string"
  :found "number"
  :message-hash "sha256:7d3e...a1f0"       ;; hash of the violating message
  :blamed "sender"                          ;; explicit blame attribution
  :verifier "@receiving-agent")             ;; who performed the check
```

The combination of `:dialect-hash`, `:message-hash`, and `:verifier` makes the blame claim independently verifiable: any party with access to the dialect definition and the message can re-run the check and confirm the violation.

**Formal property (after Moore 2016, Definition 2.3.1):** A structural contract system has *correct blame* if, for every violation error produced during structural verification, the blamed party is the party that provided the value (message or definition) that failed the check. Concretely:

- If `shape_check(msg, constraint) = Err`, then blame falls on the sender of `msg` — the agent that constructed the message.
- If `causal_check(msg, store, protocol) = Err`, then blame falls on the sender of `msg` — the agent that set the `:caused-by` reference.
- If `verify_r5(dialect) = Err`, then blame falls on the dialect author — the signer of the dialect definition.

In all cases, blame is assigned to the party whose output (message or definition) was the direct input to the failing check.

verified-by: property

Trace:
- TEST-230
- CON-205

### REQ-231: Complete Monitoring

Every message crossing a trust boundary SHALL pass through the full structural verification pipeline before acceptance. No message shall be delivered to application logic without completing all applicable checks.

The monitoring pipeline for a message in a dialect with structural contracts:

```
received bytes
  │
  ├─ 1. Parse (Layer 1 DCFL parser)              → SExpr or parse error
  ├─ 2. Validate (Layer 2–3 message grammar)      → Message or grammar error
  ├─ 3. Verify R1–R4 (if dialect definition)      → pass or R1/R2/R3/R4 violation
  ├─ 4. Install (if dialect definition)            → dialect table updated
  ├─ 5. Expand (template substitution)             → expanded SExpr
  ├─ 6a. Verify causal (REQ-203)                   → pass or CausalViolation
  ├─ 6b. Verify shape (REQ-223)                    → pass or ShapeViolation
  │
  └─ 7. Deliver to application logic
```

Complete monitoring requires:

1. **No bypass.** There is no code path from "received bytes" to "deliver to application logic" that skips steps 1–6. Every message, regardless of source, dialect, or content, enters through the parser and exits through the verification pipeline.

2. **No partial checks.** If a dialect has both a `(protocol ...)` and `(shape ...)` clause, both 6a and 6b run. A message that passes causal verification but fails shape verification is rejected. A message that passes shape verification but fails causal verification is rejected.

3. **Fail-closed.** If any step produces an error, the message is rejected. The pipeline does not continue past a failure. The error is reported with blame information (REQ-230).

4. **Dialect definitions are also monitored.** A `(meta (teach ...))` message carrying a dialect definition passes through the same pipeline. R1–R4 verification (step 3) and R5 verification (protocol/shape well-formedness) run before installation. A malformed dialect definition is rejected before it can affect future message processing.

**Formal property (after Moore 2016, Definition 2.3.2):** A structural contract system is a *complete monitor* if, for every well-formed message that reaches application logic, one of the following holds:

- The message passed all applicable structural checks (causal + shape), or
- The dialect has no structural contracts (R5 passes trivially), or
- The agent's policy explicitly skips structural verification for this dialect (opt-out documented in agent configuration).

No other path to delivery exists.

**Relationship to CBCL's existing pipeline:** The `run_pipeline()` function in `cbcl-rs` already enforces steps 1–5 as a linear chain with early termination on error. REQ-231 extends this to steps 6a and 6b, requiring that structural contract checks are integrated into the same pipeline with the same fail-closed semantics. The pipeline is the single interposition point — CBCL's equivalent of Moore's contract monitor boundary.

verified-by: example

Trace:
- TEST-231
- CON-206

### REQ-232: Blame Chain for Dialect Lifecycle

Blame attribution SHALL account for the lifecycle of a dialect definition. As a dialect propagates through the network via gossip, multiple agents participate in its lifecycle, and blame shifts accordingly:

1. **Authorship.** The dialect author (Ed25519 signer) is blamed for defects in the definition itself: malformed protocols, unsatisfiable shapes, R1–R3 violations that escape local testing.

2. **Propagation.** An agent that propagates a dialect via `(meta (teach ...))` vouches for its R1–R5 compliance. If the dialect contains defects, the propagating agent shares blame — they should have verified before retransmitting.

3. **Installation.** An agent that installs a dialect accepts responsibility for enforcing its contracts. If the agent installs a dialect without R5 verification (e.g., by disabling checks), blame for subsequent structural violations shifts from the sending agent to the installing agent.

4. **Usage.** An agent that sends a message using a dialect is blamed for violations of that dialect's contracts. The sending agent is responsible for constructing messages that satisfy the shapes and providing valid `:caused-by` references.

The blame chain is recorded in the violation error:

```scheme
(error @sender "causal-violation"
  :detail "invalid-predecessor"
  :caused-by "sha256:7d3e...a1f0"
  :expected "pause-ack"
  :found "pause"
  :blame-chain (
    (:author "@consortium" :signed "sha256:abc1...def2")
    (:propagated-by "@agent-a" :at "2026-03-20T14:00:00Z")
    (:installed-by "@agent-b" :at "2026-03-20T14:05:00Z" :r5-verified #t)
    (:sent-by "@agent-c" :message "sha256:e4f5...6789")))
```

The `:blame-chain` is a sequence of (party, action, evidence) triples tracing the dialect from authorship to the violating message. Each entry is independently verifiable: the signature can be checked, the propagation message can be looked up in the message store, and the R5 verification result can be reproduced.

**Monotonicity.** The blame chain is append-only — each lifecycle event adds an entry. It does not modify or retract prior entries. This is monotonic and coordination-free.

verified-by: example

Trace:
- TEST-232

### REQ-233: Violation Error Grammar

Violation errors produced by structural contract checks SHALL conform to the following S-expression grammar, extending the existing CBCL error format:

~~~abnf
; ================================================================
; Structural violation error format
;
; Extends the existing (error ...) performative with structured
; fields for blame attribution and independent verification.
; ================================================================

structural-error   = "(" "error" WS recipient WS violation-type
                     1*(WS error-field) ")"

violation-type     = %s"shape-violation"
                   / %s"causal-violation"
                   / %s"r5-violation"

error-field        = dialect-field / author-field / dialect-hash-field
                   / performative-field / detail-field
                   / blamed-field / verifier-field
                   / message-hash-field / blame-chain-field
                   / rule-field / field-field
                   / expected-field / found-field
                   / caused-by-field

dialect-field      = ":dialect" WS string
author-field       = ":dialect-author" WS string
dialect-hash-field = ":dialect-hash" WS string
performative-field = ":performative" WS string
detail-field       = ":detail" WS string
blamed-field       = ":blamed" WS blame-party
verifier-field     = ":verifier" WS string
message-hash-field = ":message-hash" WS string
blame-chain-field  = ":blame-chain" WS "(" 1*(WS blame-entry) ")"
rule-field         = ":rule" WS string
field-field        = ":field" WS keyword
expected-field     = ":expected" WS string
found-field        = ":found" WS string
caused-by-field    = ":caused-by" WS string

blame-party        = %s"sender" / %s"dialect-author"
                   / %s"installer"

blame-entry        = "(" 1*(WS blame-kv) ")"
blame-kv           = keyword WS s-expr
~~~

All fields are keyword parameters — legal in the existing grammar. No Layer 1 or Layer 2 changes. Violation errors are themselves valid CBCL messages, parseable by the same DCFL parser.

verified-by: property

Trace:
- TEST-233
- CON-205

### REQ-234: Observability for Blame

The system SHALL expose blame attribution in observability metrics:

- Counter `cbcl_blame_attribution_count` with labels `{dialect, blamed_party, violation_type}`.
- Histogram `cbcl_violation_error_size_bytes` tracking the size of structured violation errors.

These metrics enable operators to identify patterns: which dialects produce the most violations, which party is most often blamed, and whether violation errors are growing unreasonably large.

verified-by: n/a

Trace:
- OBS-206
- OBS-207

---

## Non-Functional Requirements

### NFR-200: Protocol Parsing Latency

Protocol declaration parsing latency SHALL be ≤ 500 ns for a protocol with ≤ 10 steps UNDER benchmark conditions (Apple M4, release build) WITH median measurement.

Trace:
- TEST-250

### NFR-201: Causal Verification Latency

Causal verification latency SHALL be ≤ 100 ns per message UNDER benchmark conditions WITH median measurement.

**Rationale:** Causal verification is a hash map lookup (find referenced message) + a set membership check (is the predecessor's performative in the valid set). Both are O(1). 100 ns provides margin over the expected ~20 ns.

Trace:
- TEST-251

### NFR-202: Shape Parsing Latency

Shape constraint parsing latency SHALL be ≤ 300 ns for a shape with ≤ 8 rules.

Trace:
- TEST-252

### NFR-203: Shape Check Latency

Runtime shape checking SHALL be ≤ 200 ns per message for a shape with ≤ 8 rules.

Trace:
- TEST-253

### NFR-204: No Mutable Protocol State

The system SHALL maintain zero bytes of mutable per-thread protocol state. Causal verification reads from the message store (append-only) and the protocol declaration (static). No `protocol_states` map.

**Rationale:** This is the concrete consequence of the monotonicity guarantee (REQ-211). Zero mutable state = no coordination required = works over unreliable transports.

Trace:
- TEST-254

### NFR-205: No Unsafe Code

All new modules SHALL compile with `#![forbid(unsafe_code)]`.

Trace:
- TEST-255

### NFR-206: No-Std Compatibility

All new modules SHALL use only `alloc` and `core`.

Trace:
- TEST-256

---

## Architecture Decisions

### ADR-001: Causal Dependencies vs DFA State Machines

**Context:** SPEC-001 compiled protocol declarations to DFA transition tables. The DFA tracked per-thread state and required message ordering. The CALM theorem identifies this as non-monotonic — it fundamentally requires coordination.

**Decision:** Replace DFA state machines with causal dependency declarations. Each message carries `:caused-by`, referencing its causal predecessor. The protocol declares which predecessor types are valid for each step.

**Trade-offs:**

| Factor | DFA (SPEC-001) | Causal (this spec) |
|---|---|---|
| Message ordering | Required | Not required |
| Mutable state | Per-thread DFA state | None |
| Coordination | Required (CALM: non-monotonic) | Free (CALM: monotonic) |
| Counted sequences | Yes | No (non-monotonic) |
| Unreliable transport | Problematic | Works |
| Expressiveness | Regular languages | DAGs |
| Message overhead | None | `:caused-by` parameter per message |
| Implementation | DFA table + state map | Hash map lookup + set membership |
| Lean formalisation | Automata theory | Graph reachability on immutable structures |

**Rationale:** CBCL operates across trust boundaries over unreliable transports (Nostr relays). The DFA's ordering requirement fights this architecture. Causal dependencies align with CBCL's zero-trust, gossip-based, order-independent design. The loss of counted sequences is acceptable: counting is aggregation, which is non-monotonic by definition — if you want it, you fundamentally need coordination.

### ADR-002: Initiator-Perspective Convention (Retained)

Protocols are declared from one perspective. The dual is not computed — causal dependencies are symmetric. If the protocol says "pause-ack :after pause," both the sender and receiver of pause-ack know the constraint. Unlike SPEC-001's session types, there is no send/recv distinction and no duality computation.

**Rationale:** Causal dependencies describe relationships between messages, not roles. "X follows Y" is the same regardless of who sends X. This eliminates the entire duality machinery (REQ-102 in SPEC-001) and the Offer variant of the AST.

### ADR-003: Structural Contracts as Optional (Retained)

Structural contracts are optional. A dialect without `(protocol ...)` or `(shape ...)` passes R5 trivially.

### ADR-004: VPL Tree Patterns for Shapes (Retained from SPEC-001)

Shape constraints use VPL tree patterns. See ADR-005 in SPEC-001.

### ADR-005: `:caused-by` as Keyword Parameter

**Context:** Causal references need to be carried in messages. Options: a new syntactic form, a wrapper message, or a keyword parameter.

**Decision:** `:caused-by` is a keyword parameter, like `:thread` and `:in-reply-to`.

**Rationale:** Keyword parameters are already legal CBCL syntax (Layer 2). No grammar extension. The parser already extracts `:thread` and `:sender` — adding `:caused-by` to the extraction list is a one-line change. The parameter is an atom (string or symbol), parsed by existing rules.

### ADR-006: Message Store as Append-Only Log

**Context:** Causal verification requires looking up referenced messages. Where are they stored?

**Decision:** The agent's existing `conversation_threads: BTreeMap<String, Vec<Message>>` serves as the message store. It is already append-only (messages are added via `append_to_thread`, never removed). Causal verification reads from this store.

A per-thread hash index (`HashMap<ContentHash, usize>`) SHALL be maintained alongside the message store, providing O(1) amortised lookup by content hash (SPEC-003 REQ-309). Appending a message whose content hash already exists is a no-op (SPEC-003 REQ-310 — deduplication, required for G-Set CRDT idempotence).

**Rationale:** The conversation thread is a per-thread append-only log. The hash index is mandatory — O(n) linear scan cannot meet the ≤ 100 ns verification latency bound (NFR-201) for threads with more than a few dozen messages. Index overhead is ~64 bytes per message (SPEC-003 NFR-303). Deduplication is required because gossip transports routinely deliver the same message via multiple paths. See SPEC-003 for the full message store specification including causal closure transfer, reconciliation, compaction, and persistence.

### ADR-007: Merkle DAG — Multi-Predecessor Causality (Fan-In)

**Context:** `:caused-by` could accept a list of hashes (enabling fan-in / merge messages) or a single hash (restricting to tree topology).

**Decision:** `:caused-by` accepts either a single value or a list of values. The concrete message graph is a Merkle DAG per thread. Fan-in (merge) is supported via `(all ...)` node references in protocol declarations and list-valued `:caused-by` in messages.

**Rationale:** Fan-in verification is monotonic. Each sub-check — "does predecessor hash H resolve to a message of type T?" — is a monotone predicate on the append-only message store. A conjunction of monotone predicates is monotone: once all predecessors exist and have the correct types, adding more messages to the store cannot invalidate the check. The CALM theorem applies: this has a consistent coordination-free distributed implementation.

The earlier draft of this ADR rejected fan-in on the grounds that it "breaks the simplicity of single-predecessor lookup" and introduces non-monotonicity. This was incorrect. The verification procedure for multi-predecessor `:caused-by` is:

1. For each hash in the list, look up the message in the store. (O(k) lookups where k = number of predecessors.)
2. Check that each predecessor's performative is a valid predecessor per the protocol's `(all ...)` declaration.
3. Check that ALL required predecessor types are present (conjunction).

Step 3 is the key insight: "all of {A, B, C} are present" is a conjunction of positive existence checks on a grow-only store. Once true, it stays true. This is monotonic — not in the trivial sense, but in the CALM-relevant sense: the verification function's output can only transition from `Err` (predecessors not yet present) to `Ok` (all present), never the reverse. Adding messages to the store can only help, never hurt.

The coordination concern is real but misplaced: the *sender* of a merge message must have observed all predecessor messages to know their hashes. But this is equally true for single-predecessor `:caused-by` — the sender must have observed the predecessor to reference its hash. Fan-in means the sender observed k messages instead of 1. The verifier remains stateless and coordination-free.

**Conjunction vs disjunction:** `(all ...)` and `(any ...)` are symmetric constructs with explicit head keywords — no bare lists. `(all ...)` uses conjunction: ALL listed items participate. `(any ...)` uses disjunction: one of the listed items participates. The two compose: `(then (all a b) (any c d))` means "after both a and b have occurred, either c or d may follow." On the right (successor) side, `(then begin (all search-a search-b search-c))` means all three searches proceed concurrently (fan-out), while `(then prepare (any vote-yes vote-no))` means the sender chooses one response. Right-side `(all ...)` exclusivity is a sender obligation — the verifier cannot enforce "at most one" monotonically (see REQ-200).

### ADR-008: Thread-Scoped Causality

**Context:** Should `:caused-by` be permitted to reference messages in other threads?

**Decision:** No. `:caused-by` hashes must resolve within the same `:thread`. Cross-thread references are a verification error.

**Rationale:** Thread-scoped causality makes each thread a self-contained, independently verifiable unit. A third party verifying thread T needs only the messages in T and the dialect definition — no knowledge of other threads is required. Cross-thread references would make verification depend on the union of multiple threads, complicating escrow and audit scenarios. Inter-thread coordination (e.g., a message in thread B that logically depends on a result in thread A) can be expressed at the application level without formal causal links.

---

## Contracts

### CON-200: CausalProtocol API

```
Interface: cbcl_core::protocol::CausalProtocol

Types:
  enum NodeRef {
      Any(BTreeSet<String>),            // disjunction: any one of these types
                                         // "begin" = protocol start (in Any set)
      All(BTreeSet<String>),            // conjunction: all of these types
                                         // Fan-in on left, concurrent fan-out on right
  }

  struct StepDecl {
      performative: String,
      predecessors: Vec<NodeRef>,        // left-side node-refs (enforceable)
                                         // multiple requirements possible
                                         // (e.g., reachable via disjunction OR join)
      successors: Vec<NodeRef>,          // right-side node-refs (declarative intent)
                                         // Any = choice, All = concurrent
                                         // populated from desugared then-decl edges
  }

  struct CausalProtocol {
      steps: Vec<StepDecl>,
  }

Methods:
  fn is_acyclic(&self) -> bool
    Post-conditions: true iff no cycle in dependency graph
    Complexity: O(|steps|²)

  fn is_reachable_from_begin(&self) -> bool
    Post-conditions: true iff every step reachable from "begin"
    Complexity: O(|steps|²)

  fn valid_predecessors(&self, performative: &str) -> Option<&BTreeSet<String>>
    Post-conditions: returns predecessor set for the performative
    Complexity: O(log |steps|)

  fn performatives(&self) -> BTreeSet<&str>
    Post-conditions: all performative names in the protocol
    Complexity: O(|steps|)

Implements:
  REQ-200, REQ-204, REQ-205

Verified by:
  TEST-200, TEST-204, TEST-205
```

### CON-201: Protocol Parser API

```
Interface: cbcl_parser::protocol_parser

Functions:
  fn parse_protocol(sexpr: &SExpr) -> Result<CausalProtocol, ProtocolParseError>
    Pre-conditions: sexpr has head symbol "protocol"
    Post-conditions: returns CausalProtocol or descriptive error
    Error model:
      - EmptyProtocol
      - MalformedStep { detail }
      - MissingAfterClause { step }
      - UndefinedPerformative { name }

Implements:
  REQ-201

Verified by:
  TEST-201
```

### CON-202: Causal Verification API

```
Interface: cbcl_core::protocol::CausalVerifier

Types:
  enum CausedBy {
      Begin,
      Single(String),                    // single predecessor hash
      Multiple(Vec<String>),             // fan-in: list of predecessor hashes
  }

Functions:
  fn verify_causal(
      msg_performative: &str,
      caused_by: &CausedBy,
      message_store: &dyn MessageStore,
      protocol: &CausalProtocol,
  ) -> Result<(), CausalViolation>
    Pre-conditions: protocol installed, message parsed
    Post-conditions:
      - Ok: causal link(s) valid (all predecessors exist and have valid types)
      - Err: CausalViolation with detail
    Mutates: nothing
    Complexity:
      - Single predecessor: O(1) amortised (hash map lookup + set membership)
      - Multiple predecessors: O(k) where k = number of predecessors
    Error model:
      CausalViolation::UnknownPredecessor { caused_by }
      CausalViolation::InvalidPredecessor { caused_by, expected, found }
      CausalViolation::MissingCausedBy
      CausalViolation::IncompleteFanIn { missing_types }
      CausalViolation::ExtraneousPredecessor { caused_by, found }
      CausalViolation::FanInWithoutAllDecl { performative }

trait MessageStore {
    fn lookup(&self, msg_id: &str) -> Option<&Message>;
}

Implements:
  REQ-203

Verified by:
  TEST-203
```

### CON-203: ShapeConstraint API

```
Interface: cbcl_core::shape::ShapeConstraint

(Identical to SPEC-001 CON-104 — retained without change.)

Implements:
  REQ-220, REQ-223, REQ-224

Verified by:
  TEST-220, TEST-223, TEST-224
```

### CON-205: Violation Error Builder API

```
Interface: cbcl_core::blame::ViolationError

Types:
  enum BlameParty {
      Sender,
      DialectAuthor,
      Installer,
  }

  enum ViolationType {
      Shape,
      Causal,
      R5,
  }

  struct BlameEntry {
      party: String,           // agent identifier
      action: String,          // "authored", "propagated", "installed", "sent"
      evidence: String,        // hash or message-id
      timestamp: Option<String>,
      r5_verified: Option<bool>,
  }

  struct ViolationError {
      violation_type: ViolationType,
      dialect: String,
      dialect_author: String,
      dialect_hash: String,
      performative: String,
      blamed: BlameParty,
      verifier: String,
      message_hash: Option<String>,
      detail: String,
      blame_chain: Vec<BlameEntry>,
      // Shape-specific fields
      rule: Option<String>,
      field: Option<String>,
      expected: Option<String>,
      found: Option<String>,
      // Causal-specific fields
      caused_by: Option<String>,
  }

Methods:
  fn from_shape_violation(
      violation: &ShapeViolation,
      dialect: &Dialect,
      msg: &Message,
      verifier: &str,
  ) -> ViolationError
    Post-conditions:
      - blamed == BlameParty::Sender
      - dialect_hash matches dialect's canonical hash
      - message_hash matches msg's canonical hash
      - All shape-specific fields populated

  fn from_causal_violation(
      violation: &CausalViolation,
      dialect: &Dialect,
      msg: &Message,
      verifier: &str,
  ) -> ViolationError
    Post-conditions:
      - blamed == BlameParty::Sender
      - caused_by field populated
      - All causal-specific fields populated

  fn from_r5_violation(
      violation: &R5Violation,
      dialect: &Dialect,
      propagator: Option<&str>,
  ) -> ViolationError
    Post-conditions:
      - blamed == BlameParty::DialectAuthor
      - blame_chain includes author entry

  fn to_sexpr(&self) -> SExpr
    Post-conditions:
      - Output is a valid CBCL (error ...) message
      - Output conforms to REQ-233 grammar
      - Parseable by the standard DCFL parser

  fn verify_blame(&self, dialect_store: &dyn DialectStore,
                   message_store: &dyn MessageStore) -> Result<(), BlameVerificationError>
    Post-conditions:
      - dialect_hash matches stored dialect
      - message_hash matches stored message (if present)
      - blame_chain entries are consistent with store
    Note: enables third-party independent verification of blame claims

Implements:
  REQ-230, REQ-232, REQ-233

Verified by:
  TEST-230, TEST-232, TEST-233
```

### CON-206: Pipeline Completeness Contract

```
Interface: cbcl_core::pipeline (extension)

Invariant (Complete Monitoring):
  For all code paths from receive_bytes() to deliver_to_application():
    1. parse() was called and returned Ok
    2. validate() was called and returned Ok
    3. If dialect definition: verify_r1_r4() was called and returned Ok
    4. If dialect definition: verify_r5() was called and returned Ok
    5. expand() was called and returned Ok
    6. If dialect has protocol: verify_causal() was called and returned Ok
    7. If dialect has shape: shape_check() was called and returned Ok

  No path exists that reaches deliver_to_application() without
  completing all applicable steps.

  Error at any step produces a ViolationError (CON-205) with correct
  blame attribution (REQ-230) and terminates the pipeline.

Functions:
  fn run_pipeline(
      input: &[u8],
      agent: &Agent,
  ) -> Result<PipelineResult, ViolationError>
    Post-conditions:
      - Ok: all applicable checks passed, message delivered
      - Err: ViolationError with blamed party identified
      - No partial delivery: either all checks pass or none
    Mutates:
      - message_store: appends accepted message (append-only)
      - dialect_table: adds dialect (if definition, grow-only)
    Does NOT mutate:
      - Any per-thread protocol state (NFR-204)

Implements:
  REQ-231

Verified by:
  TEST-231
```

### CON-204: Shape Parser API

```
Interface: cbcl_parser::shape_parser

(Identical to SPEC-001 CON-105 — retained without change.)

Implements:
  REQ-221

Verified by:
  TEST-221
```

---

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)

- `CausalProtocol::is_acyclic()` — DFS on dependency graph, returns bool
- `CausalProtocol::is_reachable_from_begin()` — BFS/DFS from "begin", returns bool
- `CausalProtocol::valid_predecessors()` — map lookup, returns option
- `verify_causal()` — lookup(s) + set membership, returns result (reads message store but does not mutate; O(k) for fan-in with k predecessors)
- `parse_protocol()` — S-expression to CausalProtocol, returns result
- `parse_shape()` — S-expression to ShapeConstraint, returns result
- `ShapeConstraint::check()` — tree walk, returns result
- `verify_r5()` — composes acyclicity + reachability + definedness + uniqueness + shape checks

### Effectful Shell (orchestrates I/O, calls pure core)

- `DialectRegistry::install()` — calls verify_r5, mutates registry
- `Agent::evaluate_and_apply()` — calls verify_causal and shape check, reads message store
- `run_pipeline()` — orchestrates parse → validate → verify → install

### Boundary Contracts

- `CausalProtocol` — pure core → shell (stored alongside dialect)
- `ShapeConstraint` — pure core → shell (stored alongside dialect)
- `CausalViolation` — pure core → shell (returned to caller)
- `ShapeViolation` — pure core → shell (returned to caller)

### Dependency Rule

Dependencies point inward. `protocol.rs` and `shape.rs` depend only on `alloc` and `core`.

---

## Test Specifications

### TEST-200: Causal Protocol Construction

Verify `CausalProtocol` construction, predecessor lookup, and performative enumeration. Cover: Compaction (7 steps), request-response loop (2 steps), document operations with choice (5 steps), scatter-gather with fan-in via `(all ...)` (7 steps), two-phase commit with fan-in (5 steps).

Trace: REQ-200

### TEST-201: Protocol Parser Round-Trip

Parse protocol S-expressions. Cover: single predecessor, `(any ...)` disjunctive predecessors, `(all ...)` conjunctive predecessors, `begin` as predecessor, right-side `(any ...)` (choice), right-side `(all ...)` (concurrent fan-out), 1–10 steps.

Negative: empty protocol, unknown head symbol, `(any ...)` with fewer than 2 arguments, `(all ...)` with fewer than 2 arguments, bare list without `any`/`all` head keyword (parse error — head keyword required).

Technique: Example-based + property-based.

Trace: REQ-201

### TEST-202: `:caused-by` Parameter Extraction

Verify that the message parser extracts `:caused-by` alongside `:thread` and `:sender`. Cover: string values, symbol values, `"begin"`, list values (fan-in with multiple hashes), missing parameter.

Trace: REQ-202

### TEST-203: Causal Verification

Scenario 1 (valid chain): pause ←caused-by→ begin, pause-ack ←caused-by→ pause. Both pass.

Scenario 2 (invalid predecessor): get-memory ←caused-by→ begin. Protocol says get-memory :after pause-ack. Rejected.

Scenario 3 (unknown message): msg ←caused-by→ "nonexistent-id". Rejected.

Scenario 4 (no protocol): dialect has no `(protocol ...)`. All messages pass.

Scenario 5 (no `:caused-by`): dialect has protocol, message lacks `:caused-by`. Per policy.

Scenario 6 (fan-in valid): merge-results ←caused-by→ (result-a-hash result-b-hash result-c-hash). Protocol declares `(then (all result-a result-b result-c) merge-results)`. All three hashes resolve to correct types. Passes.

Scenario 7 (fan-in incomplete): merge-results ←caused-by→ (result-a-hash result-b-hash). Missing result-c. Rejected with `IncompleteFanIn { missing_types: ["result-c"] }`.

Scenario 8 (fan-in extraneous): merge-results ←caused-by→ (result-a-hash result-b-hash result-c-hash extra-hash). Protocol only expects three. Rejected with `ExtraneousPredecessor`.

Scenario 9 (fan-in without declaration): msg ←caused-by→ (hash-a hash-b). Protocol has no `(all ...)` declaration for msg's performative. Rejected with `FanInWithoutAllDecl`.

Verify: no mutable state changed by any check.

Technique: Example-based + integration test.

Trace: REQ-203

### TEST-204: Acyclicity

- `(step a :after b) (step b :after a)` → rejected (direct cycle)
- `(step a :after b) (step b :after c) (step c :after a)` → rejected (transitive cycle)
- `(step a :after begin) (step b :after a) (step c :after b)` → accepted (linear chain)
- `(step a :after begin) (step b :after a) (step a :after b)` → rejected (step uniqueness fails first — REQ-207 — but acyclicity would also catch it)

Technique: Example-based.

Trace: REQ-204

### TEST-205: Reachability

- `(step a :after begin) (step b :after a) (step c :after x)` where x is not defined → rejected (c unreachable from begin, and x undefined — REQ-206 catches first)
- `(step a :after begin) (step b :after begin)` → accepted (both directly reachable)

Trace: REQ-205

### TEST-206: Performative Definedness

Protocol references `track-ack` but no `extend track-ack` exists → R5 rejects.

Trace: REQ-206

### TEST-207: Step Uniqueness

`(step a :after begin) (step a :after x)` → rejected (duplicate step for `a`).

Trace: REQ-207

### TEST-208: R5 Installation Integration

Verify `DialectRegistry::install()` calls R5 for protocols and shapes. All sub-checks produce `R5Violation`.

Trace: REQ-208

### TEST-209: DCFL Preservation (Lean 4)

Prove: installing a dialect with a causal protocol does not extend the grammar. The protocol clause is an S-expression (Layer 1). Causal verification is a predicate on immutable data, not a recogniser. DCFL preservation is trivial.

Technique: Formal proof (Lean 4).

Trace: REQ-209

### TEST-210: Structural Contract Gossip Propagation

End-to-end: Agent A defines dialect with protocol + shape. Teaches Agent B. B verifies R1–R5, installs. B's installed protocol has identical dependency graph.

Trace: REQ-210

### TEST-211: Monotonicity Property

For all valid causal checks: `verify_causal(msg, store) = Ok` implies `verify_causal(msg, store ∪ {new}) = Ok` for all `new`. Covers both single-predecessor and multi-predecessor (fan-in) messages. For fan-in: if all k predecessors are present and valid, adding any message to the store preserves validity.

Technique: Property-based.

Trace: REQ-211

### TEST-212: Thread Topology and Verification Tiers

Scenario 1 (linked list): Sequential protocol (compaction). Verify the `:caused-by` chain forms a linked list. Causal closure of the last message equals the entire thread.

Scenario 2 (tree — fan-out): Two agents reply to the same message. Verify both branches are independently valid. Causal closure of a leaf on one branch does NOT include messages from the other branch.

Scenario 3 (DAG — fan-in): Scatter-gather protocol. Three results fan-in to a merge message via `(all ...)`. Verify the merge message's causal closure includes all three result messages and their shared ancestor.

Scenario 4 (Tier 1 — incremental): Active participant receives messages one at a time. Each message is verified using only its direct predecessors (already in store). Verify no DAG traversal is needed for incremental verification.

Scenario 5 (Tier 2 — causal closure): Agent joins thread mid-conversation at message M. Compute causal closure of M. Verify that the closure is sufficient to validate M without the full thread. Verify that messages NOT in the closure are not needed.

Scenario 6 (Tier 3 — full audit): Third-party verifier receives all messages in a thread. Reconstructs DAG. Verifies all causal links. Detects a tampered message (modified content, hash mismatch). Detects an incomplete thread (missing message referenced by `:caused-by`).

Scenario 7 (topology detection): Given a set of messages, classify the thread topology as linked list, tree, or DAG based on fan-out/fan-in presence.

Technique: Example-based + integration testing.

Trace: REQ-212

### TEST-230: Correct Blame Attribution

Scenario 1 (shape violation — sender blamed): Message `(track-shipment 42)` sent to agent with shape `(require :package string)`. Violation error blames sender. `:blamed` is `"sender"`. `:dialect-author` is `"@consortium"`. `:field` is `":package"`. `:expected` is `"string"`. `:found` is `"number"`.

Scenario 2 (causal violation — sender blamed): Message with `:caused-by "msg-001"` where msg-001 is a `pause` but protocol expects `pause-ack`. Violation error blames sender. `:blamed` is `"sender"`. `:expected` is `"pause-ack"`. `:found` is `"pause"`.

Scenario 3 (R5 violation — dialect author blamed): Dialect definition with shape referencing undefined performative. Violation error blames dialect author. `:blamed` is `"dialect-author"`. `:dialect-hash` matches the submitted definition.

Scenario 4 (third-party verification): Given a violation error and access to the dialect definition + message, a third party calls `verify_blame()` and confirms the violation independently. The check succeeds (blame is correct). Modify the dialect hash in the error — `verify_blame()` now returns `BlameVerificationError`.

Technique: Example-based + property-based (for all generated violations, blamed party matches the party whose output failed the check).

Trace: REQ-230

### TEST-231: Complete Monitoring

Scenario 1 (no bypass): Construct a message that would pass shape checking but fail causal checking. Verify it is rejected — both checks run, causal failure prevents delivery.

Scenario 2 (no bypass, reverse): Construct a message that would pass causal checking but fail shape checking. Verify it is rejected.

Scenario 3 (dialect definition monitoring): Submit a `(meta (teach ...))` with a dialect whose protocol has a cycle. Verify R5 rejects before installation. The dialect is NOT in the dialect table after rejection.

Scenario 4 (fail-closed): Submit a message where the DCFL parser succeeds but template expansion exceeds R2 bounds. Verify the message is rejected and no partial state change occurred (message store unchanged, dialect table unchanged).

Scenario 5 (coverage): Instrument `run_pipeline()` with step counters. For every message that reaches delivery, assert that all applicable check counters incremented. For every rejected message, assert that the pipeline terminated at the failing step.

Technique: Integration testing + coverage instrumentation.

Trace: REQ-231

### TEST-232: Blame Chain Construction

Scenario 1 (full lifecycle): Agent A authors and signs dialect. Agent A teaches Agent B. Agent B installs (R5 verified). Agent C sends a message using the dialect that violates a shape. Violation error's `:blame-chain` contains four entries: authored (A), propagated (A), installed (B, r5-verified: true), sent (C).

Scenario 2 (unverified installation): Agent B installs dialect with R5 verification disabled. Agent C sends a conforming message, but it fails a shape check due to an unsatisfiable constraint. Blame chain shows installed (B, r5-verified: false) — blame shifts to installer.

Scenario 3 (monotonicity): Verify that each lifecycle event only appends to the blame chain. No entry is modified or removed after creation.

Technique: Integration testing.

Trace: REQ-232

### TEST-233: Violation Error Grammar Conformance

For every violation error produced by `ViolationError::to_sexpr()`:

1. Parse the output with the standard DCFL parser — must succeed.
2. Validate against the REQ-233 ABNF grammar — must conform.
3. Extract `:blamed` — must be one of `"sender"`, `"dialect-author"`, `"installer"`.
4. Extract `:dialect-hash` — must be a valid SHA-256 prefixed string.
5. Round-trip: parse the error, reconstruct a `ViolationError`, re-serialize — output must be identical.

Technique: Property-based (generate random violations, verify grammar conformance).

Trace: REQ-233

### TEST-220–225: Shape Constraints

(Identical to SPEC-001 TEST-120–126, renumbered. Same coverage, same techniques.)

Trace: REQ-220–225

### TEST-250–256: Performance and Non-Functional

Criterion benchmarks for NFR-200–203. Compilation checks for NFR-205–206.

Trace: NFR-200–206

---

## Observability

### OBS-200: Protocol Parse Duration

Metric: `cbcl_protocol_parse_duration_ns` (histogram).

### OBS-201: Causal Verification Duration

Metric: `cbcl_causal_verify_duration_ns` (histogram). Per-message causal check cost.

### OBS-202: Causal Violations

Counter: `cbcl_causal_violation_count` with labels `{dialect, performative, violation_type}`.

### OBS-203: Shape Parse Duration

Metric: `cbcl_shape_parse_duration_ns` (histogram).

### OBS-204: Shape Check Duration

Metric: `cbcl_shape_check_duration_ns` (histogram).

### OBS-205: Shape Violations

Counter: `cbcl_shape_violation_count` with labels `{dialect, performative, violation_type}`.

### OBS-206: Blame Attribution Count

Counter: `cbcl_blame_attribution_count` with labels `{dialect, blamed_party, violation_type}`.

Tracks how often each party is blamed, per dialect. Enables operators to distinguish between bad senders (frequent `sender` blame) and bad dialect definitions (frequent `dialect-author` blame).

### OBS-207: Violation Error Size

Histogram: `cbcl_violation_error_size_bytes`. Tracks the serialised size of structural violation errors. Blame chains grow with dialect propagation depth — this metric detects unbounded growth.

---

## Implementation Plan

### Phase 1: Pure Core — Causal Protocols (cbcl-core)

1. `src/protocol.rs` — `CausalProtocol`, `StepDecl`, `is_acyclic()`, `is_reachable_from_begin()`, `valid_predecessors()`
2. `src/causal.rs` — `verify_causal()`, `CausalViolation`, `MessageStore` trait
3. Tests (TEST-200, TEST-203, TEST-204, TEST-205, TEST-211)

### Phase 2: Pure Core — Shapes (cbcl-core)

4. `src/shape.rs` — `ShapeConstraint`, `ShapeRule`, `check()`, `no_duplicate_keywords()`
5. Tests (TEST-220–224)

### Phase 3: R5 Verification (cbcl-core)

6. `src/r5.rs` — `verify_r5()` composing protocol + shape checks
7. Tests (TEST-208, TEST-222)

### Phase 4: Parser (cbcl-parser)

8. `src/protocol_parser.rs` — `parse_protocol()` from S-expression
9. `src/shape_parser.rs` — `parse_shape()` from S-expression
10. Extend `src/dialect_parser.rs` — handle `(protocol ...)` and `(shape ...)` clauses
11. Extend `src/pipeline.rs` — add R5 check
12. Tests (TEST-201, TEST-221)

### Phase 4b: Blame and Monitoring (cbcl-core)

8b. `src/blame.rs` — `ViolationError`, `BlameParty`, `BlameEntry`, `from_shape_violation()`, `from_causal_violation()`, `from_r5_violation()`, `to_sexpr()`, `verify_blame()`
8c. Tests (TEST-230, TEST-232, TEST-233)

### Phase 5: Agent Integration (cbcl-core)

13. Extend `Dialect` struct — add `protocol: Option<CausalProtocol>`, `shapes: Vec<ShapeConstraint>`
14. Extend `Agent::evaluate_and_apply()` — extract `:caused-by`, call `verify_causal()`, call shape check
15. Tests (TEST-202, TEST-203, TEST-210, TEST-223)

### Phase 6: Verification (lean-cbcl)

16. `LeanCbcl/Protocol.lean` — CausalProtocol, acyclicity, reachability
17. `LeanCbcl/Causal.lean` — verify_causal, monotonicity proof
18. `LeanCbcl/Shape.lean` — shape constraint AST, VPL checking
19. Extend `LeanCbcl/DcflPreservation.lean` — protocol + shape cases (trivial for causal)
20. `LeanCbcl/Blame.lean` — correct blame property: for all violations, blamed party == source of failing input
21. `LeanCbcl/CompleteMonitoring.lean` — complete monitoring property: all delivery paths pass through full pipeline
22. Proofs (TEST-209, TEST-225, TEST-230, TEST-231)

### Phase 7: Performance and Polish

21. Criterion benchmarks (TEST-250–256)
22. Fuzz targets: `fuzz/fuzz_targets/protocol_parser.rs`, `fuzz/fuzz_targets/shape_parser.rs`
23. Grammar update (`docs/cbcl-grammar.ebnf`)
24. IETF Internet-Draft update — add `:caused-by` parameter semantics

---

## Verification Strategy

| Component | Techniques |
|---|---|
| Causal protocol (pure core) | Property-based (acyclicity, reachability, monotonicity) + mutation testing |
| Protocol parser | Fuzzing + property-based (roundtrip) |
| Causal verification | Property-based (monotonicity: adding messages never invalidates — covers both single and fan-in) + example-based |
| Shape constraint (pure core) | Property-based + mutation testing |
| Shape parser | Fuzzing + property-based (roundtrip) |
| Runtime shape checking | Example-based + integration testing |
| Correct blame (REQ-230) | Property-based (for all violations, blamed party == party whose output failed) + example-based |
| Complete monitoring (REQ-231) | Integration testing + coverage instrumentation (every delivery path passes all checks) |
| Blame chain (REQ-232) | Integration testing (lifecycle scenarios) + property-based (append-only) |
| Violation error grammar (REQ-233) | Property-based (all generated errors parse as valid CBCL + conform to ABNF) |
| DCFL preservation | Formal proof (Lean 4) — simpler than SPEC-001 (no automata theory) |
| Monotonicity (CALM) | Property-based (∀ msg, store, new: Ok(msg,store) → Ok(msg, store∪{new})) — covers single-predecessor and fan-in (∧ of monotone predicates) |
| Performance | Criterion benchmarks |

---

## What This Specification Explicitly Defers

1. **Counted sequences** ("exactly N rounds then close"). Non-monotonic (aggregation). Requires coordination per CALM. Could be added as an opt-in extension that acknowledges the ordering requirement.
2. **Protocol delegation** (passing causal references across protocol boundaries). Future work.
3. **Value predicates in shapes** (e.g., `price > 0`). Requires arithmetic, outside DCFL.
4. **Multiparty causal protocols**. Binary causal links only. Multiparty requires a global causal graph — possible but adds complexity.
5. **Hash algorithm agility**. REQ-202 specifies SHA-256 for content addressing. Future revisions may support algorithm negotiation (e.g., SHA-3, BLAKE3) via the `:signature-algorithm` metadata on dialects.
6. **Message store garbage collection**. The append-only message store grows without bound. Compaction (removing old messages) is non-monotonic and requires coordination. Deferred to application policy.

---

## Appendix A: Complete ABNF Grammar Extension

~~~abnf
; ================================================================
; CBCL Structural Contracts Grammar Extension (Layers 4a + 4b)
;
; Layer 4a: Causal protocol declarations
; Layer 4b: Shape constraints
;
; Both extend dialect-clause (Layer 3).
; Both are S-expressions parsed by Layer 1.
; Both are monotonic (CALM-safe).
;
; Parser class: LL(1) / DCFL (unchanged).
; ================================================================

; --- Layer 3 modification ---
;
;   dialect-clause =/ protocol-clause / shape-clause
;
; The existing sig-algorithm-clause (":signature-algorithm",
; formerly ":protocol") is unchanged. "protocol" (symbol) and
; ":signature-algorithm" (keyword) dispatch deterministically.

; --- Layer 4a: Causal protocol ---

protocol-clause  = "(" "protocol" 1*(WS then-decl) ")"

then-decl        = "(" "then" 2*(WS node-ref) ")"
                 ; Variadic. Pairwise left-to-right: each node-ref
                 ; may follow the previous. When either side is a
                 ; list, the Cartesian product of edges applies.
                 ; Minimum 2 arguments.

node-ref         = performative-ref
                 / "(" "any" 2*(WS performative-ref) ")"
                 / "(" "all" 2*(WS performative-ref) ")"
                 ; Atom = single step in the chain.
                 ; (any ...) = alternatives (disjunction).
                 ; (all ...) = conjunction.
                 ; Both require minimum 2 arguments.

performative-ref = "begin" / symbol
                 ; "begin" = protocol start (no prior message).
                 ; symbol = performative name.
                 ; MUST match an extend clause in this dialect
                 ; or an installed ancestor (REQ-206).

; --- Layer 4b: Shape constraints ---

shape-clause     = "(" "shape" WS performative-name
                   1*(WS shape-rule) ")"

performative-name = symbol

shape-rule       = require-rule / optional-rule
                 / max-depth-rule

require-rule     = "(" "require" WS keyword
                   [WS type-constraint]
                   *(WS shape-rule) ")"

optional-rule    = "(" "optional" WS keyword
                   [WS type-constraint]
                   [WS default-value]
                   *(WS shape-rule) ")"

max-depth-rule   = "(" "max-depth" WS number ")"

type-constraint  = "string" / "number" / "bool"
                 / "symbol" / "keyword" / "list"

default-value    = s-expr
~~~

### Grammar Statistics

| Metric | Protocol (4a) | Shape (4b) | Total |
|---|---|---|---|
| New productions | 4 (`protocol-clause`, `then-decl`, `node-ref`, `performative-ref`) | 6 (`shape-clause`, `shape-rule`, `require-rule`, `optional-rule`, `max-depth-rule`, `type-constraint`) | 10 |
| New keywords | 4 (`protocol`, `then`, `all`, `begin`) | 4 (`shape`, `require`, `optional`, `max-depth`) | 8 |
| Modified rules | 1 (`dialect-clause` +2) | 0 | 1 |
| Layer 1 changes | 0 | 0 | 0 |
| Parser class impact | None | None | None — LL(1) / DCFL |

### Worked Example: Compaction Dialect

```scheme
(meta (define compaction (cbcl) @supervisor
  (:resource-requirements
    ((max-depth 16)
     (max-expansion-size 4096)
     (verification-time 500)))
  (extend pause (reason)
    (tell @agent (control-msg :action "pause" :reason reason)))
  (extend pause-ack ()
    (reply @supervisor (control-ack :action "pause")))
  (extend get-memory ()
    (ask @agent "dump-context"))
  (extend memory-dump (content)
    (reply @supervisor content))
  (extend set-memory (content)
    (tell @agent (control-msg :action "set-memory" :content content)))
  (extend set-memory-ack ()
    (reply @supervisor (control-ack :action "set-memory")))
  (extend resume ()
    (tell @agent (control-msg :action "resume")))
  (protocol
    (then begin pause pause-ack get-memory
      memory-dump set-memory set-memory-ack resume))
  (shape pause
    (require :reason string))
  (shape memory-dump
    (require :content list))
  (:signature-algorithm "ed25519")))
```

Usage with `:caused-by`:

```scheme
(lang compaction (pause "context full" :caused-by "begin" :thread "t-1"))
;; → msg-001

(lang compaction (pause-ack :caused-by "msg-001" :thread "t-1"))
;; → msg-002

(lang compaction (get-memory :caused-by "msg-002" :thread "t-1"))
;; → msg-003

;; Invalid: skips pause-ack
(lang compaction (get-memory :caused-by "msg-001" :thread "t-1"))
;; → (error @sender "causal-violation"
;;     :detail "invalid-predecessor"
;;     :caused-by "msg-001"
;;     :expected "pause-ack"
;;     :found "pause")
```

### Worked Example: Scatter-Gather with Fan-In

```scheme
(meta (define parallel-search (cbcl) @coordinator
  (:resource-requirements
    ((max-depth 8)
     (max-expansion-size 2048)
     (verification-time 200)))
  (extend dispatch ()
    (tell @coordinator (control-msg :action "dispatch")))
  (extend search-a (query)
    (ask @worker-a query))
  (extend search-b (query)
    (ask @worker-b query))
  (extend search-c (query)
    (ask @worker-c query))
  (extend result-a (data)
    (reply @coordinator data))
  (extend result-b (data)
    (reply @coordinator data))
  (extend result-c (data)
    (reply @coordinator data))
  (extend merge-results (combined)
    (tell @coordinator combined))
  (protocol
    (then begin dispatch)
    (then dispatch (search-a search-b search-c))
    (then search-a result-a)
    (then search-b result-b)
    (then search-c result-c)
    (then (all result-a result-b result-c) merge-results))
  (:signature-algorithm "ed25519")))
```

Usage with fan-in `:caused-by`:

```scheme
(lang parallel-search (dispatch :caused-by "begin" :thread "t-2"))
;; → sha256:1111...

(lang parallel-search (search-a "find widgets" :caused-by "sha256:1111..." :thread "t-2"))
;; → sha256:2222...
(lang parallel-search (search-b "find widgets" :caused-by "sha256:1111..." :thread "t-2"))
;; → sha256:3333...
(lang parallel-search (search-c "find widgets" :caused-by "sha256:1111..." :thread "t-2"))
;; → sha256:4444...

;; Fan-out: three searches independently caused by the same dispatch.
;; Each is valid — fan-out is permitted (REQ-212).

(lang parallel-search (result-a (widgets 42) :caused-by "sha256:2222..." :thread "t-2"))
;; → sha256:5555...
(lang parallel-search (result-b (widgets 17) :caused-by "sha256:3333..." :thread "t-2"))
;; → sha256:6666...
(lang parallel-search (result-c (widgets 8) :caused-by "sha256:4444..." :thread "t-2"))
;; → sha256:7777...

;; Fan-in: merge-results caused by ALL three results.
;; :caused-by is a list of hashes — one per required predecessor.
(lang parallel-search
  (merge-results (combined 67)
    :caused-by ("sha256:5555..." "sha256:6666..." "sha256:7777...")
    :thread "t-2"))
;; → sha256:8888...
;; Verifier checks: (all result-a result-b result-c) requires
;; all three types present. Hash 5555 → result-a ✓,
;; 6666 → result-b ✓, 7777 → result-c ✓. Passes.

;; Invalid: missing result-c
(lang parallel-search
  (merge-results (combined 59)
    :caused-by ("sha256:5555..." "sha256:6666...")
    :thread "t-2"))
;; → (error @sender "causal-violation"
;;     :detail "incomplete-fan-in"
;;     :missing ("result-c"))
```
