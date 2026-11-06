---
id: SPEC-035
title: Register semantics, ordering policies and trust assumptions
version: 0.1.0
status: draft
last-updated: 2026-11-06
---

# Register semantics, ordering policies and trust assumptions

## Orientation

Intent: make a state rule's conflict behavior and trust assumptions explicit before
extending the kernel-correctness proofs. The named failure is **agreement without
useful arbitration**: replicas can consistently select a hash winner that is
neither the most recent write nor an authorized resolution of a conflict.

[[SPEC-019-state-rules]] currently defines `last`, `latest-per-key`,
`latest-per-signer` and `register-per-key` using greatest content address. This
proposal separates replacement, grouping and arbitration. It explores explicit
last-writer-wins, conflict-preserving and ownership-based contracts. It does not
select HLC over the alternatives, introduce a clock field, rename installed
rules, or change the existing runtime or corpus.

Example: Alice and Bob concurrently write different titles. A last-writer-wins
contract selects the greatest declared order key under its clock assumptions.
A multi-value contract returns both candidates; an authorized later write can
explicitly replace them. An owned contract permits only the declared owner to
write. These are different contracts, not different implementations of one
universal notion of “last.”

The proof target remains **kernel denotational correctness**: for every modeled
well-formed clause and address-consistent accepted history, its interpretation
satisfies an independent specification of its declared rules. Arbitrary business
correctness, Rust correspondence and liveness are separate obligations.

Controls: [[SPEC-035-register-semantics#REQ-3500]] semantic naming;
[[SPEC-035-register-semantics#REQ-3501]] explicit ordering assumptions;
[[SPEC-035-register-semantics#REQ-3502]] replacement authority;
[[SPEC-035-register-semantics#REQ-3503]] conflict visibility;
[[SPEC-035-register-semantics#REQ-3504]] proof and resource boundaries;
[[SPEC-035-register-semantics#REQ-3505]] versioned migration.

Next actor: CBCL maintainer selects the contracts and ordering profiles through
[[SPEC-035-register-semantics#ADR-3500]] before authorizing runtime changes.
Reviewer path: Orientation, decisions, open questions. Implementer path: contract,
tests, requirements. Paper-author path: proof target and claim boundaries.

## Amendment Channels

The user's instruction authorizes a draft on a branch from latest main. It does
not resolve the open design choices below. Existing installed semantics remain
those of [[SPEC-019-state-rules]]. An accepted runtime amendment must follow its
major-specification and corpus-version rule. Neither a new name nor a proof may
silently change the meaning of an installed dialect.

## Current behavior and candidate names

These names are candidates, not accepted new grammar. Here last-writer-wins means
selection by a specified immutable order key; an HLC is one possible order key.
It does not promise an objectively latest real-world concurrent event.

| Existing construct | Existing meaning | Candidate contract/name |
|---|---|---|
| `last` | Greatest address across all selected writes of a verb | `lww-register` when cross-writer overwriting and timestamp ordering are intended |
| `latest-per-key` | Greatest address per application key, without replacement selection | `lww-map` for a precisely specified per-key last-writer-wins contract |
| `latest-per-signer` | Same-signer observed replacement, then greatest address among survivors | `lww-per-signer` if remaining own conflicts are resolved by a declared order key |
| `register-per-key` | Observed replacement and optional deletion, then greatest address per key | Candidate consolidation into `lww-map`, only after replacement/deletion semantics are settled |
| `values` | Distinct values of surviving explicitly unreplaced writes | `multi-value-register` |
| `values-per-key` | Distinct surviving values per key, with optional deletion | `multi-value-map` |
| Role-constrained writer | Existing role checks restrict who can write | An `owned-register` pattern; a new primitive is justified only if existing roles plus a register are insufficient |
| `bounded-counter` | Separately authorized resource operations and tagged observations | Retain name and its profile-specific assumptions |

A multi-value result can coalesce equal values. The immutable act history still
retains the separate signed acts and their provenance. A conflict-inspection API needs separate candidate-act access when provenance is required.
An immutable field drawn only from the unique opener needs no cross-writer clock.
A per-key grouping does not, by itself, assign ownership of that key.

## ADR-3500: Separate conflict policy from ordering mechanism

Status: proposed. Grouping determines which writes concern one entry. Explicit
replacement determines which candidates survive. Arbitration, if selected,
determines which surviving candidate is displayed. Authority determines permitted writers and resolvers; it is not inferred from the order key.

The recommended design direction is to retain conflict-preserving rules and offer
explicit last-writer-wins rules where overwriting is acceptable. Trust in authorized
senders is a legitimate candidate assumption for the latter. No universal Byzantine
writer guarantee is implied. Resolve field semantics before proving them correct.

| Ordering/resolution option | Useful meaning | Assumptions and limits |
|---|---|---|
| HLC | Causality-respecting order with approximate physical-time interpretation | Correct clock generation/update, physical-clock/skew policy for recency claims, stable timestamp evidence; concurrent events still require a tie-breaker; Byzantine writers can inflate timestamps |
| Lamport clock | A logical order consistent with the evidence observed by honest writers | Correct generation/update; no wall-clock recency guarantee; concurrent events require a tie-breaker; unchecked writers can inflate counters |
| Per-signer sequence | Successive updates by one signer | Durable nonforking issuance or an explicit fork policy; numbers from different signers do not establish cross-signer recency |
| Derived dependency rank | Checkable order relative to declared authenticated dependencies | Exact rank is computed from evidence, not accepted as an unchecked assertion; omitted observations remain unknowable; a writer can manufacture chains; equal-rank branches remain concurrent |
| Explicit replacement without a clock | Writes supersede precisely the permitted named candidates | Replacement scope and authority must be defined; concurrent survivors remain visible unless a separate policy resolves them |
| Semantic merge | A declared union, maximum or other fixed combination | The domain-specific combination must express the intended meaning and stay within a checked rule vocabulary; numerical maximum is not intrinsically fair or truthful |
| Owner-assigned version | One authorized role controls an entry | Trust in that role and issuance discipline; same-key multiple devices and equivocation need explicit treatment |
| Quorum-certified version | Consistent certified choice under a witness policy | Authentication, durable voting and fault-bound assumptions; may stall; not supplied by merely carrying a timestamp |
| Content-address arbitration | Reproducible arbitrary selection without clock state | No recency, fairness or overwrite-authority guarantee; writers can vary admissible content to influence hashes |

HLC and Lamport timestamps must be immutable message evidence if they affect the
fold. A receiver's arrival time or local current clock cannot decide the result.
A sender signature authenticates an asserted timestamp, not honest clock behavior.
A future-skew check against receipt-time wall clocks can make replicas disagree or
change a verdict over time. Such checks need a separately justified policy.

Open, owner CBCL maintainer: select profiles, exact total order and tie-breaker,
range/overflow handling, clock persistence/restarts, validation and trust scope.
For dependency-derived order, decide whether the evidence is protocol `:caused-by`,
semantic `:replaces`, or a distinct relation. R5's same-verb predecessor restrictions
mean these relations cannot be treated as interchangeable.

## ADR-3501: Do not conflate a map with replacement authority

Status: proposed. `last` across all members explicitly permits cross-member
arbitration. Honest clocks can support that policy, but cannot justify it.
Similarly, two members writing one application key share a conflict domain;
the key does not authorize either to override the other.

Retain same-signer isolation for per-signer registers. For a shared per-key register, decide who can replace observed writes:
every authorized writer, only the owner, or a separate resolution role.
An ownership pattern first reuses existing role/cast checks; it is not
an automatic new register operator. Collective resource ownership continues to
follow its own contracts rather than register overwrite policy.

Open, owner CBCL maintainer: determine whether `latest-per-key` is retired,
retained under its existing meaning, or migrated to the same replacement model as
`register-per-key`. Consolidation must specify tombstones, missing groups and
concurrent write/delete behavior; a rename alone is insufficient.

## Requirements for an accepted successor

These obligations constrain a future adopted amendment. They do not change
current installation or receipt behavior.

### REQ-3500: Semantic names

An adopted name MUST identify last-writer-wins, conflict preservation or ownership
without presenting hash arbitration as physical recency. The amendment MUST give
each old rule an explicit retain, retire or migrate disposition.
Trace: [[SPEC-035-register-semantics#TEST-3500]].

### REQ-3501: Ordering assumptions

Every single-value arbitration contract MUST specify its immutable order key,
comparison, equal-key tie-breaker, empty behavior and trust premises. It MUST
separate convergence, causal ordering, approximate recency and fairness claims.
Any clock read MUST occur in the host before pure binding/folding; the pure core
MUST consume explicit evidence rather than reading a clock. Timestamp wire fields,
canonical encoding, bounds and forgery controls MUST be specified before runtime
implementation. No wire syntax is introduced by this draft.
Trace: [[SPEC-035-register-semantics#TEST-3501]].

### REQ-3502: Replacement and authority

An adopted contract MUST independently specify grouping, supersession, arbitration
and write/resolution authority. Per-signer replacement MUST preserve signer
isolation. Superseded admitted acts MUST retain their replacement effects;
domain-excluded acts MUST contribute neither values nor replacement effects.
The full admitted replacement source MUST remain distinct from a displayed subset.
Trace: [[SPEC-035-register-semantics#TEST-3502]].

### REQ-3503: Conflict-preserving observations

Conflict-preserving contracts MUST retain all unreplaced admissible concurrent
values rather than selecting an arbitrary winner. The contract MUST state equal-value
coalescing, deletion, absent values, support and provenance-access behavior. A
single-value presentation MUST NOT silently redefine the authoritative multi-value
state or pretend a hidden candidate was explicitly resolved.
Trace: [[SPEC-035-register-semantics#TEST-3503]].

### REQ-3504: Correctness and trust boundaries

Kernel correctness MUST mean agreement with independently defined semantics for
the enumerated covered grammar, not only set invariance. An arbitrary-clause
claim MUST have a coverage/translation argument connecting each covered rule to
its interpretation. Proofs MUST expose assumptions and distinguish typed model
correctness from Rust/wire/rendering correspondence and business refinement.
Register clock-trust assumptions MUST NOT be attributed to bounded-counter
certification or used as a substitute for resource authorization. Byzantine
resource guarantees MUST remain scoped to the relevant model and its premises.
Trace: [[SPEC-035-register-semantics#TEST-3504]].

### REQ-3505: Versioned migration

Any adopted change to the kernel vocabulary, ordering or binding MUST advance
[[SPEC-019-state-rules]] and the conformance corpus together as required there.
Old signed dialects and histories MUST retain their old interpretation. New
identities, authoring compilation, bindings and migration behavior MUST be
specified and tested before activation. This draft MUST NOT activate new rules.
Trace: [[SPEC-035-register-semantics#TEST-3505]].

## CON-3500: Proof and implementation handoff

This document introduces no external-input API. Its tables describe candidate
contracts, not executable syntax. A future accepted grammar must enumerate the
constructors and typed observations before parsing, binding or evaluation changes.
Reuse [[SPEC-019-state-rules#Contracts]], [[SPEC-019-state-rules#CON-1906]] and
[[SPEC-025-consensus-free-refinement#CON-2501]] with their distinct scopes.

The proof work starts with independent membership specifications for
selections and independent reduction specifications. Prove domain/source filtering,
replacement and grouping laws separately from arbitration. For each adopted
arbitration profile, prove that selection returns exactly its specified result.
Then compose these into a clause theorem with explicit coverage for events,
map support, histogram, sum, protocol progress and the separately verified resource
extension. Missing coverage is an open obligation, never an implicit universal claim.

Purity boundary: hosts generate clock evidence, authenticate, persist and send;
the core interprets immutable acts. New proofs add no runtime clock or state.
Initialization, parsing, JSON rendering, deployed cryptography and universal Rust
correspondence require their own arguments. No application-wide invariant follows
solely from correct register interpretation.

Implements: [[SPEC-035-register-semantics#REQ-3501]],
[[SPEC-035-register-semantics#REQ-3502]],
[[SPEC-035-register-semantics#REQ-3504]],
[[SPEC-035-register-semantics#REQ-3505]].

## Acceptance tests for the eventual amendment

These are specified future obligations, not executed implementation evidence.

### TEST-3500: Naming and disposition (core)

Given every current register rule, identify the proposed successor or explicit
retention. Reject an unexplained rename or a “latest” claim derived solely from
hash order. Validates: [[SPEC-035-register-semantics#REQ-3500]].

### TEST-3501: Ordering profiles (core; clock-recovery integration is depth)

For each adopted profile, check sequential writes, empty input, duplicate/reordered
delivery, cross-signer behavior and its evidence boundaries. Timestamp profiles
add equal timestamps, restart and numeric boundaries. Demonstrate an inflated
Byzantine timestamp defeating an honest-clock premise; do not label it
Byzantine-safe arbitration. Sequence and dependency profiles instead test forks
and fabricated dependency evidence against their specified checks. Re-evaluating
the same acts later or on another receiver must not change the result. Validates:
[[SPEC-035-register-semantics#REQ-3501]].

### TEST-3502: Scope and replacement (core)

An observed edit supersedes the permitted prior candidates even if its content
hash is lower. Another signer cannot retire an own-register entry. A superseded
replacer still retires its targets. An excluded replacer retires none. Exercise
same-key cross-member writes, delayed targets, concurrent deletion and missing
replacement references according to the adopted contract. Exercise more current
candidates than `max-list`: the existing binder names only a bounded prefix, so
one edit does not necessarily replace every observed candidate. Validates:
[[SPEC-035-register-semantics#REQ-3502]].

### TEST-3503: Conflicts and resolution (core)

Concurrent distinct values remain visible under the multi-value contract. An
authorized resolution naming both removes both; a later previously unseen write
remains a candidate. Check equal-value coalescing and provenance access separately.
A display-only winner must not erase authoritative conflicts. Validates:
[[SPEC-035-register-semantics#REQ-3503]].

### TEST-3504: Proof coverage and falsification (core; Rust equivalence is depth)

Independently inspect the declared grammar and its coverage inventory. Changing a
covered interpreter branch to drop candidates, allow cross-signer replacement or
reverse arithmetic must invalidate its corresponding correctness proof. A constant
output must not satisfy the independent specification. Audit final theorem premises
and axioms. Keep resource safety and conditional progress claims separate from
register timestamp assumptions. Validates:
[[SPEC-035-register-semantics#REQ-3504]].

### TEST-3505: Migration and inactivity (core; host migration is depth)

Verify this draft changes no runtime, canonical dialect body or corpus. Before an
adopted release, replay old histories with the pinned old semantics; install new
contracts under their new identities and corpus version; reject mixed-version
interpretation. Validates: [[SPEC-035-register-semantics#REQ-3505]].

## Research evidence

- [[register-ordering-research]] records primary sources and separates their
  results from CBCL design inferences.
- [[SPEC-019-state-rules]] supplies current hash order, supersession, domains,
  pure intent construction and amendment requirements.
- [[SPEC-025-consensus-free-refinement]] and
  [[SPEC-034-owned-progress-closure]] supply resource safety/refinement and the
  separately scoped correct-owner liveness result. Neither makes ordinary
  timestamp registers Byzantine-safe.

## Draft review evidence

[[register-semantics-draft-review]] records independent review, Orientation
comprehension, source-branch provenance and documentation validation. It is not
acceptance of the unresolved design choices.

## Open decisions and next work

Owner: CBCL maintainer. Select names and profiles, decide cross-member overwrite
policy, settle per-key replacement/deletion consolidation, and specify clock or
sequence metadata only for the chosen profile. Then amend the standing spec,
produce an implementation plan, and resume kernel correctness against those
independent contracts. The existing runtime remains governed by the standing spec
until that amendment. Human review can accept a clock-trusting register profile
without weakening the separately specified resource-certification profile.
