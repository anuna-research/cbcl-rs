---
id: BUG-012
title: Product-read composition is promised without an authored contract
severity: S3
priority: P1
status: new
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer and dialect API maintainer
component: specs/SPEC-038-lvar-state-kernel.md
---

# BUG-012: Product-read composition has no complete contract

[[SPEC-038-lvar-state-kernel#REQ-3809]] requires the derived post-map menu to
include conjunction and comparison of monotone reads, and gives the product
condition `(and (count approvals 2) (exists closed))` as an example.
[[SPEC-038-lvar-state-kernel#CON-3800]] labels its algebra abstract, with no new
wire syntax, and omits these post-map constructors. The authored threshold
contract [[SPEC-038-lvar-state-kernel#CON-3801]] names one field and elements.
The native `Rule` and `lattice::Post` inventories contain no conjunction or
comparison constructor. This is an incomplete contract and implementation gap,
not a claim that the parser violates its current grammar.

Internal products already exist: Rust `Term::Pair`/`L::Pair` and Lean plan pairs
are implemented. Their existence does not supply the missing closed post-map
operations or an authored product read. No claim is made that every equivalent
business condition is inexpressible using a purpose-built finite lattice.

## Reproduced native recognition

A temporary parser example invoked the public strict `parse` and `parse_state`
functions, then was removed. Each input was a recognized S-expression.

```text
existing-leaf-reads: accepted
compound-threshold: threshold takes: name field element…
derived-conjunction: unknown rule 'and' (SPEC-019 REQ-1901)
```

The accepted control is:

```lisp
(state
  (approvals (count approve))
  (closed (exists close))
  (threshold enough approvals (count 2))
  (threshold closing closed #t))
```

The rejected candidates replace the two thresholds with the proposed form below,
or append `(ready (and enough closing))` to the accepted control. These candidates
are proposals, not existing syntax. The evidence also includes the complete enum
inventories in `crates/cbcl-core/src/state.rs` and
`crates/cbcl-core/src/lattice.rs`, and the threshold dispatcher in
`crates/cbcl-parser/src/state_parser.rs`.

## Reviewable authored proposal — not approved grammar

Retain every existing single-field declaration and add a named conjunction of
existing, independently typed leaf reads:

```lisp
(state
  (approvals (count approve))
  (closed (exists close))
  (threshold ready
    (and (read approvals (count 2))
         (read closed #t))))
```

Proposed grammar extension:

```text
entry     := existing-entry | '(' 'threshold' name condition ')'
condition := '(' 'read' field element ')'
           | '(' 'and' condition condition+ ')'
```

Each leaf reuses the existing element grammar and source-relative admission
checks. Sources must be actual field declarations preceding the condition; named
threshold outputs are not new leaf sources. Define size(read field element)=1
and size(and children)=1+sum(size(child)). The complete condition must fit the
installed max-list bound; existing scalar/string/number bounds still apply to
elements. Recognition precedes evaluation. This proposal adds
no state-dependent contribution or selector and no host callback.

Proposed observations: a fault from any dependency takes precedence and unions
canonical evidence; otherwise the conjunction is pending until every leaf is
reached; success is `{"status":"reached","element":true}`. The successful
Boolean denotes the entire declared condition. Repeated leaves do not count as
additional approvals. Source freeze scopes and dependency faults use the same
kernel paths as individual reads. Empty and unary conjunctions reject.

A compound threshold is an observation, not a new source field: a freeze
declaration targeting its name rejects, matching the current single-field
threshold restriction. Authors freeze its leaf source fields instead. Each leaf
uses its source's own installed freeze and read scope; the compound adds no
shared cut. Every existing leaf eligibility restriction remains in force,
including rejection of supersede-frozen threshold sources. Clause-wide freeze
collection must prevent declaration order from bypassing that check.

Leaf comparisons use the already permitted monotone threshold tests, such as
count >= a fixed bound. Comparing two growing counters with `a >= b` is not
monotone in general; this proposal does not silently admit such comparisons.
Whether additional comparisons of immutable/frozen values belong in this
contract must be explicit before implementing them.

## Decisions and acceptance

The dialect API maintainer chooses whether conjunction/comparison is an authored
capability in this specification, or only a closed internal algebra capability
with authored exposure reserved for a later contract. The latter requires an
explicit clarification of the example and scope in
[[SPEC-038-lvar-state-kernel#REQ-3809]]; it is not an inferred deferral.

For authored support, amend the two contracts with recognized grammar, result
shape, comparison restrictions and dependency/freeze rules, then implement the
Rust parser/installation/kernel/schema/bindings and the Lean source/plan/oracle
path. Acceptance extends [[SPEC-038-lvar-state-kernel#TEST-3800]] and
[[SPEC-038-lvar-state-kernel#TEST-3801]] with conjunction growth, fault-first
propagation, earlier-field/type rejection, revisable/signed source rejection,
freeze scopes, duplicate delivery and deliberate semantic mutants.

The implementer keeps the contract-dependent slice unimplemented until that
choice is recorded. Independent work on existing requirements continues. Full
SPEC-038 completion must not treat the current primitive inventory as satisfying
this unresolved requirement.
