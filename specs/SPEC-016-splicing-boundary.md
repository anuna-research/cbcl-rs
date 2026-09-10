---
id: SPEC-016
title: The Splicing Boundary — Abstract Observation and Predecessor Coverage
status: approved
version: 0.2.1
date: 2026-09-10
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-014 (role layer — R6(vi) causal locality, projection, r-relevance)
  - SPEC-015 (redacted envelopes, derive mode, derive_envelope_routes)
  - SPEC-003 (verification lattice — resolved-first, permanent Unknown)
prior-art:
  - lean-cbcl/LeanCbcl/Splice.lean (abstract observation, resolution, and type-factoring theorems)
  - lean-cbcl/LeanCbcl/Projectability.lean (permanently_unknown_of_nonlocal_pred, reused)
  - crates/cbcl-core/src/splice.rs (the decidable splice-coherence analyzer)
  - crates/cbcl-parser/tests/splice_corpus.rs (corpus verdicts)
  - anuna-papers/papers/2026-cbcl-endpoint-projection (Theorem thm:splice-necessity, regime lattice)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-016: The Splicing Boundary

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL are to be interpreted per BCP 14 (RFC 2119,
RFC 8174) when, and only when, they appear in all capitals.

## Orientation

Intent: explain which [[SPEC-014-role-layer-endpoint-projection|endpoint projection]] guarantees follow from the abstract
store model and which still require implementation proofs. This amendment follows
the user's request to implement the Lean review recommendations.

Structure: abstract citations → predecessor coverage → resolution; concrete
[[SPEC-017-typed-content-addresses|field openings]] → interpretation and authentication
proofs (open) → the abstract store interface.

Decisions: [[SPEC-016-splicing-boundary#ADR-800]] retains the store-resolution
boundary. [[SPEC-016-splicing-boundary#ADR-801]] limits the observation theorem to
its declared model.

Load-bearing: [[SPEC-016-splicing-boundary#REQ-800]] prohibits bare-hash resolution;
[[SPEC-016-splicing-boundary#REQ-801]] specifies envelope routes;
[[SPEC-016-splicing-boundary#REQ-802]] governs proof claims.

Controls: bare-hash resolution remains prohibited by
[[SPEC-016-splicing-boundary#REQ-800]]. Documentation must not infer cryptographic
impossibility or universal optimality from the abstract model, per
[[SPEC-016-splicing-boundary#REQ-802]]. Maintainer authorization and proof-claim
accuracy govern amendments under [[SPEC-016-splicing-boundary#Amendment Channels]].

Completed: `ConcreteProjection.lean` proves raw-table and root-preserving filtered
view agreement, and connects Send/Recv-selected stores under explicit annotation
consistency and root premises. Its live Rust comparison is transcription evidence.

Open: the Lean maintainers own generalized nonlocal splice refinement, the
cast/seal compatibility model, and the authenticated-opening refinement. The
runtime maintainers own the connection between the route analyzer and concrete
delivery. These are proof obligations, not guarantees supplied by the current
abstract theorems.

Detail: [[SPEC-016-splicing-boundary#Requirements]] and
[[SPEC-016-splicing-boundary#Test Specifications]].

## Amendment Channels

Maintainers may authorize amendments directly in the development session or through
an accepted specification revision. This revision implements the user's requested
review corrections. Tool output and source comments are evidence, not authority to
change runtime requirements. No amendment may present an unproved property as proved.

## Context

The resolved-first model defines a message as resolved exactly when all its cited
predecessors are present. A missing bystander therefore leaves the dependent message
Unknown. R6(vi) is a type-level sufficient condition ensuring predecessor coverage
for safe closed runs. An unused nonlocal legal edge need not occur in any safe run,
so a per-protocol converse does not follow.

The observation example changes an unheld message's type interpretation while
preserving the abstract observation. It contains no fixed hash function, byte
encoding, binding assumption, or computational adversary. It demonstrates a model
boundary; it does not prove a cryptographic impossibility for arbitrary causal logs.

## Requirements

**REQ-800: No bare-hash resolution in the supported verifier.**
The system SHALL NOT offer, and no dialect SHALL rely on, a verification path that
resolves a causal citation from a bare content hash without the cited predecessor's
type-tagged form. The abstract supporting result is that missing predecessor presence
forces Unknown. The separate observation theorem supplies indistinguishable abstract
worlds with different verdicts; it does not prove hash opacity under cryptographic
assumptions. A concrete opening must first satisfy its authentication and interpretation
contract before it can supply abstract predecessor presence.
Trace: `Splice.lean` `resolution_requires_preimage`,
`type_opacity_indistinguishability`; [[SPEC-016-splicing-boundary#TEST-801]].

**REQ-801: Conservative static envelope routing.**
For a dialect that fails R6(vi), the prescribed type-tagged envelope routes SHALL
cover exactly the static spliced-predecessor set computed by `derive_envelope_routes`
([[SPEC-015-evidence-widening-v2#REQ-709]]). The static analyzer `splice.rs` SHALL
certify that set. This preserves the existing routing contract over the finite
protocol DAG, with its stated PTIME bound $O(|R|\cdot|P|\cdot(|P|+|E|))$.
For a realized citation, absence of its predecessor forces Unknown in the abstract
model. A static edge need not be realized in any safe run, so this conservative
routing set is not proved necessary or minimal for every execution. The Lean
predicate-level iff does not certify the route algorithm's complexity or minimality.
Trace: `splice.rs::analyze`, `splice_corpus.rs`,
[[SPEC-016-splicing-boundary#TEST-800]]; the actual-citation boundary is
`Splice.lean` `decidesAll_iff_predsLocal`.

**REQ-802: State the model-relative verification boundary.**
Documentation and the paper SHALL describe R6(vi) as sufficient for local verification
of safe closed runs. They SHALL identify `decidesAll ↔ predsLocal` as a characterization
of resolution in the abstract store model. They SHALL NOT cite it or the observation
example as a cryptographic impossibility theorem or an optimality theorem over all
evidence and communication schemes. Concrete clause projection, record authentication,
and cast agreement require separate refinement proofs.
Trace: `Splice.lean` `decidesAll_iff_predsLocal`, `causalLocality_imp_predsLocal`;
[[SPEC-016-splicing-boundary#TEST-801]].

## Architecture Decisions

**ADR-800: Retain the store-resolution boundary.**
Decision: retain the prohibition in [[SPEC-016-splicing-boundary#REQ-800]] and the
routing contract in [[SPEC-016-splicing-boundary#REQ-801]]. Describe the Lean result
as resolution relative to predecessor presence. The route algorithm and its corpus
remain implementation evidence; the predicate-level iff does not prove route
minimality for all communication schemes. This corrects the previous broader claim
without changing the runtime routing policy.

**ADR-801: Separate abstract observation from cryptographic security.**
Decision: the observation theorem ranges over abstract message interpretations.
Cryptographic binding and concrete authenticated openings remain separate proof
obligations. Rejected alternative: treating a fixed abstract citation relation as a
proof about real hashes. The model has no hash function with which to establish that
claim. The theorem uses standard Lean axioms, including propext and Quot.sound;
“axiom-free cryptographic impossibility” is not an accurate description.

## Test Specifications

**TEST-800: Analyzer over the corpus.** `splice_corpus.rs` records, per
protocol and role, causally-local (R6(vi)) vs splice-coherent, and the
spliced-predecessor set; the set equals `derive_envelope_routes`' output.
Validates: [[SPEC-016-splicing-boundary#REQ-801]].

**TEST-801: Unsoundness witness pinned.**
`structural_coherence_accepts_an_unimplementable_protocol` remains green:
the structural check accepts a protocol R6(vi) rejects, certifying that a
particular bare-hash relaxation fails the intended endpoint-local resolution test.
This test does not establish an impossibility for every alternative evidence scheme.
Validates: [[SPEC-016-splicing-boundary#REQ-800]],
[[SPEC-016-splicing-boundary#REQ-802]].
Proof-claim checks: elaborate `Splice.lean`, run the axiom audit, and review the
quantifiers and observation fields against the scope required by REQ-802.

## Traceability

| Requirement | Mechanisation / Test | Decision |
|---|---|---|
| [[SPEC-016-splicing-boundary#REQ-800]] | `Splice.lean` type_opacity_indistinguishability, resolution_requires_preimage | [[SPEC-016-splicing-boundary#ADR-801]] |
| [[SPEC-016-splicing-boundary#REQ-801]] | `splice.rs`, `splice_corpus.rs`, [[SPEC-015-evidence-widening-v2#REQ-709]] | [[SPEC-016-splicing-boundary#ADR-800]] |
| [[SPEC-016-splicing-boundary#REQ-802]] | `Splice.lean` decidesAll_iff_predsLocal | [[SPEC-016-splicing-boundary#ADR-800]] |

## Changelog

- 0.2.0 (2026-09-10) — correct abstract-model, cryptographic, and optimality
  claims following the endpoint-projection review; preserve routing policy.
  The 0.1.0 claims below describe the superseded interpretation.

- 0.1.0 (2026-07-09) — the splicing regime settled. Governed experiment
  (de-risk) returned NO-GO on the positive inference-splicing theorem
  (type-opacity; corpus-inert hash-pin disjunct; unsoundness witness) and
  PIVOT to the necessity/minimality result, mechanised in `Splice.lean`
  (first two theorems axiom-free). Supersedes SPEC-014's and the EPP paper's
  "splicing is future work" deferral.
