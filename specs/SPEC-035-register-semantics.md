---
id: SPEC-035
title: Register semantics, ordering policies and trust assumptions
version: 0.1.0
status: implemented
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
last-writer-wins, conflict-preserving and ownership-based contracts. The accepted extension adds explicit HLC-based LWW rules and multi-value aliases.
Existing rule names retain their meaning and identity. Alternatives remain research
context rather than selectable runtime profiles.

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

Next actor: CBCL maintainer reviews implementation against
[[SPEC-035-register-semantics#ADR-3502]]. Other clock profiles remain deferred.
Reviewer path: Orientation, decisions, open questions. Implementer path: contract,
tests, requirements. Paper-author path: proof target and claim boundaries.

## Amendment Channels

The user authorizes implementation on this branch and selects host-supplied HLCs,
retaining all existing rules and adding explicit LWW rules. Existing installed semantics remain
those of [[SPEC-019-state-rules]]. This runtime amendment follows its
major-specification and corpus-version rule. Neither a new name nor a proof may
silently change the meaning of an installed dialect.

## Retained behavior and explicit new names

The new LWW heads and multi-value aliases are adopted by
[[SPEC-035-register-semantics#ADR-3502]]. Old heads remain supported. Here
last-writer-wins means selection by an immutable host-supplied HLC order key.
It does not promise an objectively latest real-world concurrent event.

| Existing construct | Existing meaning | Extension disposition |
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

Status: accepted separation; the implemented mechanism is
[[SPEC-035-register-semantics#ADR-3502]]. Grouping determines which writes concern one entry. Explicit
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

The selected HLC order, recognition, range and host persistence boundary are
[[SPEC-035-register-semantics#ADR-3502]]. Alternative profiles remain research,
not runtime options.
For dependency-derived order, decide whether the evidence is protocol `:caused-by`,
semantic `:replaces`, or a distinct relation. R5's same-verb predecessor restrictions
mean these relations cannot be treated as interchangeable.

## ADR-3501: Do not conflate a map with replacement authority

Status: accepted scope distinction. `last` across all members explicitly permits cross-member
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

## Requirements

These obligations govern the additive HLC extension. Old rules retain their
existing contracts; the extension is activated only by explicit new rule heads.

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
implementation. The accepted wire grammar is [[SPEC-035-register-semantics#ADR-3502]].
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
specified and tested before activation. New LWW semantics MUST require explicit new heads; old signed definitions MUST
retain their original interpretation.
Trace: [[SPEC-035-register-semantics#TEST-3505]].

## CON-3500: Proof and implementation handoff

The accepted extension uses the existing dialect/message recognizers and state
exports, with the rule and clock grammar in
[[SPEC-035-register-semantics#ADR-3502]]. No new transport endpoint is introduced.
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

## Acceptance tests

Implementation evidence is [[register-semantics-implementation-review]].
The broader whole-kernel theorem remains explicitly open.

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

Verify old canonical dialect bodies and observations remain identical to main.
Replay old histories with their pinned semantics; install explicit new contracts
under their identities and corpus version. Older implementations reject new LWW
heads rather than interpreting them as legacy rules. Validates: [[SPEC-035-register-semantics#REQ-3505]].

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

Owner: CBCL maintainer. HLC semantics are adopted below, with all old heads retained.
Consolidation/retirement of old heads, alternative clocks, certified registers and
a new ownership primitive are deferred. Whole-kernel denotational correctness
requires the coverage/translation work in this contract; the HLC arbitration proof
is a component result. The resource-certification profile keeps its own assumptions.


## ADR-3502: Accepted host-HLC extension

Status: accepted by user task and explicit profile selection on 2026-11-06.
The implementation adds these rules; no existing head is removed or reinterpreted.

```text
rule := (lww-register verb value-key clock-key)
      | (lww-per-signer verb value-key clock-key)
      | (lww-map verb key-key value-key clock-key [delete-verb])
      | (multi-value-register verb value-key)
      | (multi-value-map verb key-key value-key [delete-verb])
clock := "hlc-" lowerhex{16} "-" lowerhex{8}
```

The clock is a string-valued required application field named explicitly by each
LWW rule. It encodes unsigned physical milliseconds (u64) and a logical component
(u32) in fixed-width lowercase hexadecimal. Leading zeroes are required. Thus
clock comparisons are exact without JSON number precision or the ordinary numeric
field bound limiting epoch milliseconds. Normal max-string limits still apply;
installation rejects an LWW clock bound too short for the canonical spelling.
The clock keyword differs from grouping and value keywords and cannot be a routing
or compiler-owned field. All referenced shapes and scalar-key checks still apply.
Missing, malformed, uppercase or non-string clocks are message-local shape errors.
There is no comparison to receipt time, no freshness check and no honesty verdict.

Order is lexicographic `(physical, logical, authenticated signer, content address)`.
Signer and address only break exact clock ties; they establish no fairness.
`lww-register` selects over all domain-admitted writes of its verb and returns
Absent when none exist. `lww-per-signer` uses existing same-signer supersession
before clock arbitration. `lww-map` uses existing keyed supersession and optional
delete semantics before clock arbitration. A delete carries only its key and
compiler-supplied replacements, not a clock. Concurrent unnamed additions survive
deletion; a writer includes observed current deletions as before. Superseded
replacers retain their effects; excluded replacers have none. The bounded prefix
policy for replacement binding is unchanged.

A malformed candidate supplied directly to the low-level total fold is ineligible
for LWW choice; this does not authorize effects or substitute for admission. Its
replacement references follow the ordinary admitted-history precondition. Exported
admission and intent reject malformed clocks before accepted use. Clock fields are
ordinary declared host input, never silently generated by the binder. Pure checked
HLC advancement helpers accept explicit wall-clock values, retain no global state,
and return an error on logical overflow. Hosts persist and merge clocks; shared-key
multi-device issuance requires host coordination. Honest HLC generation/update is
a trust premise of recency/causal-order claims, not a theorem about arbitrary senders.

`multi-value-register` and `multi-value-map` are parser/authoring aliases for
`values` and `values-per-key`. Their canonical internal heads remain the old heads,
so equivalent definitions have the same body identity. Describe/read-back APIs
return the canonical old operation names. A separate ownership primitive is not
added: existing roles/casts express authorized writers without another engine.

The state specification and corpus advance to major version 3. Existing canonical
encoding remains version 5: all old constructs encode identically and keep their
body hashes. Old runtime versions fail closed on new LWW heads; old heads continue
to run unchanged in the new runtime. Bindings use the shared state frames; JSON
contract version 3 remains accepted and gains explicit camelCase operations.

Scope: implement parser, installation/receipt checks, fold, binder, canonical
identity, schema, describe/authoring and corpus integration. Add independent model
proofs for the HLC arbitration operation and its replacement-source composition;
do not label these the still-open whole-kernel denotational correctness theorem.
The general coverage/translation work remains owned by the CBCL maintainer.
Trace: [[SPEC-035-register-semantics#REQ-3500]],
[[SPEC-035-register-semantics#REQ-3501]],
[[SPEC-035-register-semantics#REQ-3502]],
[[SPEC-035-register-semantics#REQ-3503]],
[[SPEC-035-register-semantics#REQ-3504]],
[[SPEC-035-register-semantics#REQ-3505]].
