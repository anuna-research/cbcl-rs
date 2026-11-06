---
title: Register semantics draft review
mode: explanation
status: draft-reviewed
last-updated: 2026-11-06
---

# Register semantics draft review

## Scope and status

[[SPEC-035-register-semantics]] and [[register-ordering-research]] are a design
draft. They do not amend installed semantics or implement a new clock profile.
The branch starts at fetched origin/main commit
`45bd3d06d141b6a10b3337544c724e6e04ffc4b1`. The original checkout and its
untracked files remain outside this isolated worktree.

The kernel-correctness investigation is paused at the semantic-design boundary.
A preliminary selection/reduction proof experiment from this session was not
included: it is incomplete and does not establish whole-clause coverage. This
branch makes no new completed-proof claim.

## Independent adversarial review

Fresh-context reviewer `/root/register_draft_review` examined the draft and
research note against the standing state specification. Its mandate covered
incorrect current semantics, hidden adoption of HLC, Byzantine-claim confusion,
replacement scope, proof scope and migration. It reported no blocking findings.

The reviewer requested profile-specific acceptance cases and explicit coverage
of bounded replacement binding. Both clarifications are incorporated: timestamp
cases apply to timestamp profiles, other profiles test their evidence/fork rules,
and the replacement case covers candidates exceeding `max-list`.

This is tool-session review, not a distinct signed Elephant peer or human approval.
The maintainer still owns the open decisions recorded in the draft.

## Orientation comprehension

Fresh-context reader `/root/register_orientation` read only the Orientation.
It correctly predicted unchanged current runtime, no adopted HLC, conflict
preservation versus single-value selection, owned-write restrictions and the
separate business/Rust/liveness boundaries. It identified ADR-3500 as the next
clock-profile decision artifact. It reported no material comprehension ambiguity.

## Validation

The controlled-language checker passed for the specification. The documentation-mode
checker passed for the research explanation. A separate local check resolved the
new wikilink targets and their heading anchors; zetl alone does not validate anchors.

`zetl --no-cache -d . check --fail-on error` remains unsuccessful on pre-existing
repository diagnostics. A baseline run with the draft files temporarily excluded
produced the same pre-existing dead links and SPL errors, with no syntax or
predicate errors.
The machine results are in `proofs/register-semantics/register-semantics-draft-validation.json`.
No new diagnostics in those categories were introduced by the draft.

`git diff --check` passed. Changed paths are documentation only. Runtime tests
were not run because the branch changes no executable implementation or corpus.

## Next actor

The CBCL maintainer selects names, conflict policies and ordering profiles through
[[SPEC-035-register-semantics#ADR-3500]]. Future implementation follows its
requirements, versioned migration and kernel-proof coverage obligations.
