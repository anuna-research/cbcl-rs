---
id: SPEC-016
title: The Splicing Boundary — Why Envelope-Widening Is Necessary, Not Convenient
status: approved
version: 0.1.0
date: 2026-07-09
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-014 (role layer — R6(vi) causal locality, projection, r-relevance)
  - SPEC-015 (redacted envelopes, derive mode, derive_envelope_routes)
  - SPEC-003 (verification lattice — resolved-first, permanent Unknown)
prior-art:
  - lean-cbcl/LeanCbcl/Splice.lean (the three theorems; first two axiom-free)
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

[[SPEC-014-role-layer-endpoint-projection|SPEC-014]] left one regime open:
\emph{splicing} --- a role verifying a causal dependency it never received,
the projection erasing the intervening \emph{bystander} messages and closing
the causal edge through them. Classical endpoint projection's whole
difficulty lives here (the non-deciding participant, merge/mergeability), so
whether CBCL could do it was the open question, and reviewers of the EPP
paper read v1's avoidance of it (R6(vi) causal locality) as a convenient
sidestep.

This spec records the settled answer, reached by a governed experiment
([[PROTO-001|USDD]] Experiment-before-Specify: splicing scored High on both
novelty and correctness-risk). The answer is a **negative** result, and a
stronger one than the hoped-for positive theorem:

> **Inference-splicing is impossible in this substrate.** A content hash is
> \emph{type-opaque}: a role holding a message's bare `:caused-by` citation
> learns nothing about the cited predecessor's type. So no role-local
> computation can recover the verdict of a message whose predecessor it does
> not hold. The only sound remedy is to deliver the predecessor's
> \emph{type-tagged} form --- full message or redacted envelope
> ([[SPEC-015-evidence-widening-v2|SPEC-015]]) --- and causal locality
> R6(vi) is thereby the \emph{forced weakest} sound coordination-free
> condition, not a simplification.

The experiment first tried to rescue a positive theorem via a candidate
condition (\emph{splice-coherence}, with a content-addressing-specific
"hash-pinned choice" disjunct). It failed soundly: the disjunct is inert on
the entire corpus and, taken as a bare-hash rule, accepts an unimplementable
protocol that R6(vi) correctly rejects (`splice.rs`
`structural_coherence_accepts_an_unimplementable_protocol`). The de-risk
verdict was NO-GO on the positive theorem and PIVOT to the necessity result.

## Context

| Regime | Observation | Status |
|---|---|---|
| R6(vi) causal locality | every predecessor delivered in full | sound (Theorem 2, SPEC-014) |
| Envelope-widening (derive) | predecessor's payload-free \emph{type-tagged} header | sound and \emph{minimal} ([[SPEC-015-evidence-widening-v2#REQ-709]]) |
| Inference-splicing | only the bystander's \emph{hash} | **impossible** ([[#REQ-800]]) |

The three regimes form a lattice on \emph{how little a role may observe};
this spec fixes its bottom.

## Requirements

**REQ-800: Type-opacity impossibility (settled, mechanised).**
The system SHALL NOT offer, and no dialect SHALL rely on, a verification
path in which a role resolves a causal citation from a bare content hash
without holding the cited predecessor's type-tagged form. This is not a
policy choice but a proved impossibility: `Splice.lean`
`type_opacity_indistinguishability` (axiom-free) exhibits two protocol
worlds indistinguishable to a role --- identical held messages, cited
hashes, and held-message types --- in which one r-relevant message is
`Valid` in one and `Violation` in the other, differing only in an unheld
predecessor's type; hence no function of a role's observation computes the
verdict.
Trace: `Splice.lean` `type_opacity_indistinguishability`,
`resolution_requires_preimage`.

**REQ-801: Envelope-widening is necessary and minimal.**
For a dialect that fails R6(vi), the set of type-tagged envelope routes that
makes it verifiable under partial delivery SHALL be exactly the set of
spliced predecessors --- necessary (each, absent, leaves a permanent
`Unknown`) and sufficient. `derive_envelope_routes`
([[SPEC-015-evidence-widening-v2#REQ-709]]) SHALL compute this minimal set,
and the static analyzer `splice.rs` SHALL certify it. The analyzer is a pure
decidable function (PTIME, $O(|R|\cdot|P|\cdot(|P|+|E|))$) over the finite
protocol DAG.
Trace: `splice.rs::analyze`, `splice_corpus.rs`,
`Splice.lean` `weakest_sound_condition`.

**REQ-802: R6(vi) is the forced weakest sound condition.**
Documentation and the paper SHALL present R6(vi) as the weakest sound
coordination-free condition under which every r-relevant verdict decides,
not as a restriction to be apologised for. `Splice.lean`
`weakest_sound_condition` proves `decidesAll ↔ predsLocal`, with R6(vi) the
no-bystanders special case.
Trace: `Splice.lean` `weakest_sound_condition`,
`causalLocality_imp_predsLocal`.

## Architecture Decisions

**ADR-800: Settle splicing negatively rather than defer it.**
*Decision*: replace SPEC-014's and the paper's "left to future work" splicing
deferral with the proved impossibility + minimality result.
*Rationale*: the honest result is stronger than the deferral. A necessity
theorem converts the reviewers' "you sidestepped the hard part" into "the
hard part is provably unavoidable here, and the minimal remedy is
characterised." *Alternative rejected*: forcing the positive theorem ---
unsound (accepts unimplementable protocols), and it would destroy the
paper's machine-checked-honesty value.

**ADR-801: Type-opacity is the load-bearing fact.**
*Decision*: the impossibility rests on content hashes being type-opaque, not
on any weakness of the verifier. *Consequence*: the result is
substrate-general --- it holds for any content-addressed causal log ---
which is why it belongs as a theorem, not an implementation note.

## Test Specifications

**TEST-800: Analyzer over the corpus.** `splice_corpus.rs` records, per
protocol and role, causally-local (R6(vi)) vs splice-coherent, and the
spliced-predecessor set; the set equals `derive_envelope_routes`' output.

**TEST-801: Unsoundness witness pinned.**
`structural_coherence_accepts_an_unimplementable_protocol` remains green:
the structural check accepts a protocol R6(vi) rejects, certifying that a
bare-hash relaxation is unsound (the NO-GO evidence, kept as a regression).

## Traceability

| Requirement | Mechanisation / Test | Decision |
|---|---|---|
| [[#REQ-800]] | `Splice.lean` type_opacity_indistinguishability, resolution_requires_preimage | [[#ADR-801]] |
| [[#REQ-801]] | `splice.rs`, `splice_corpus.rs`, [[SPEC-015-evidence-widening-v2#REQ-709]] | [[#ADR-800]] |
| [[#REQ-802]] | `Splice.lean` weakest_sound_condition | [[#ADR-800]] |

## Changelog

- 0.1.0 (2026-07-09) — the splicing regime settled. Governed experiment
  (de-risk) returned NO-GO on the positive inference-splicing theorem
  (type-opacity; corpus-inert hash-pin disjunct; unsoundness witness) and
  PIVOT to the necessity/minimality result, mechanised in `Splice.lean`
  (first two theorems axiom-free). Supersedes SPEC-014's and the EPP paper's
  "splicing is future work" deferral.
