---
title: Byzantine resource agreement — additional literature
mode: explanation
---

# Byzantine resource agreement — additional literature

The literature search changes the candidate comparison in
[[SPEC-020-resource-certification#ADR-2001]]. Whole-set agreement is one way to
protect a shared budget; conservative validator signing budgets are another.
Neither is implemented in CBCL. The maintainer's next action is a model
comparison, not a generic BGLA implementation.

## Stingray: the strongest additional candidate

[Stingray (2025), sections 3–6](https://arxiv.org/html/2501.06531v1) uses
conservative validator signing budgets and explicit reservation accounting.
Owner-signed version updates reference certified transactions. Finality requires
quorum effects evidence; local execution alone is insufficient. Its bounded-counter version merges differ from FastUnlock,
which uses fallback consensus for owned-object contention. The model has n=3f+1
validators, at most f Byzantine, and owner-discipline assumptions for progress.
Its lower-bound result does not establish CBCL's joint rights/headroom semantics.

Own fixed-version check: with n=4, f=1, quorum 3, balance 3 and local budget 2,
every certified unit debit consumes at least two honest signatures. The honest
signature capacity is six, allowing at most three certified unit debits. Giving
every validator the full balance instead permits the earlier overspending attack.
When Byzantine witnesses withhold, budget 2 permits only two unit payments before
a version update; safety does not imply full-balance availability in one version.

`check_signing_budgets.py` enumerates the small unit-debit case. This is not a
validation of the paper's version or recovery algorithms. Rounding, residual
reservations, replay, persisted budgets and cross-version certification remain
explicit model obligations for CBCL. Account rights and validator signing budgets
are distinct resources: the former authorize spending; the latter constrain witness
certification. They must not share an interchangeable balance field in an API.

## Invariant confluence: decide where agreement is necessary

[Coordination Avoidance in Database Systems (2014)](https://arxiv.org/abs/1402.2237)
analyses invariant confluence as a criterion for coordination-free execution in its
database model. The property concerns reachable states, allowed transactions and
the merge operation together; ordinary commutativity alone is insufficient.
It does not establish Byzantine monetary safety.

[Interactive Checks for Coordination Avoidance (2018)](https://www.vldb.org/pvldb/vol12/p14-whittaker.pdf)
adds interactive checking and segmented invariant confluence, using coordination
at segment transitions. Its Lucy prototype addresses common constraints including
escrow. This is a non-Byzantine modelling reference, not a witness protocol.

CBCL inference: classify resource operations by their invariant and required
evidence. Avoid a permanent label such as "all pay messages need global consensus". State the safe region and the transition that replenishes it. A compiler
can eventually report known-safe patterns or unmet proof obligations; these papers
do not justify automatically certifying arbitrary authored effects.

## Byzantine eventual consistency: separate dissemination from scarce rights

[Byzantine Eventual Consistency (2020), sections 2–3 and 5](https://arxiv.org/pdf/2012.00472)
characterizes invariant-preserving replication with arbitrary numbers of Byzantine
replicas using I-confluence. It develops Byzantine causal broadcast. It explicitly
identifies nonnegative-balance payment deductions as non-I-confluent in that model.
The result does not remove monetary validation or Sybil-resistance assumptions.

CBCL inference: an authenticated proposal/evidence DAG can be replicated separately
from the smaller committee that authorizes scarce-resource consumption. The evidence
layer tolerating equivocation does not imply that its proposals are final. This
supports the evidence/agreement/finalization split already selected in
[[SPEC-020-resource-certification#ADR-2001]]. Payload availability and bounded storage
still require explicit host contracts.

## FastPay: a concrete sequential baseline

[FastPay (2020), section 4.1](https://arxiv.org/pdf/2003.11506) provides
per-account consistent broadcast, portable transfer certificates and confirmation
relayed by a sender, recipient or proxy. The proxy is trusted for progress rather
than payment safety. Equivocating senders can lock their accounts. Authority
checks include the pending transfer, sequence, amount and balance.

CBCL inference: use this as a concrete reference for the fixed-slot baseline's
client/host lifecycle, rather than designing every relay and recovery stage from
signature counting. FastPay's payment-specific finality reasoning cannot simply
be inherited by CBCL's more general mint/burn/headroom operations.

## OrderlessChain: scope-limited corroboration

[OrderlessChain (2023 revision), abstract](https://arxiv.org/abs/2210.01477)
is a permissioned system for Byzantine execution of I-confluent applications.
It is relevant to generic CBCL rules whose invariants are independently shown to
be I-confluent. Abstract-level screening does not establish a bounded-counter
solution, so it is not promoted as a replacement protocol here.

## Revised candidate selection

| Candidate | Advantage to model | Cost or boundary to measure |
|---|---|---|
| Sequential fixed-slot / FastPay-like | Smallest account-chain change | Compatible same-account siblings still compete; recovery is limited |
| CryptoConcurrency-style compatible sets | Accept concurrency that fits certified funds | Matching-set retries, accept/close races, owner-local fallback and quorum-notarized recovery |
| Stingray-style validator budgets | Certify concurrent operations without matching the whole debit set | Conservative usable budget, version transitions, outstanding reservations, rounding and contention recovery |
| Generic BGLA / BEC evidence | Replicate and reason about growing evidence | Evidence agreement is not resource finality |

Recommendation: keep invariant-aware account-local certification as the preferred
family, with compatible sets and validator budgets as head-to-head model candidates.
Model budgets first because the safety-accounting mechanism is a direct alternative
to the reproduced quorum-subset failure. This is a research priority, not a claim
that the full budget protocol is simpler or superior. Compare both against
[[SPEC-020-resource-certification#TEST-2006]] before choosing a runtime contract.

The optional ceiling adds a coupled second budget to either adaptation. One atomic
operation certificate must authorize all its effects. A burn cannot create mint
capacity before it is final, and an issuer's headroom cannot bypass issuer authority.
Shared logical accounts with different signing keys need a separate authorization
design; concurrent devices with the same identity are the first model target.

## Evidence and next actors

The ar-crawl provenance manifest is `outputs/resource-literature/crawl-manifest.json`.
Raw successful crawls stay at the local paths in that manifest; they are not vendored
paper text. The author-page crawl corrected an initial nonexistent publications
index; the Stingray abstract DNS failure succeeded on retry outside the sandbox.
The PDF studies above were inspected through the web PDF reader as well.
This is a targeted literature search, not a claim of exhaustive coverage.

Elephant theory `spec-020-resource-agreement` records comparison, literature and
next-model tasks with sources and TEST-derived acceptance. It supersedes the
premature runtime commitment in `spec-019-bounded-counter`; that task remains
blocked by the agreement model, not completed. The built-in discovery families
record the signing-budget finding and recovery-notarization requirement.

The CBCL maintainer owns the next model and eventual protocol selection. Independent
review and reproducible finite checks are recorded in
[[bounded-counter-agreement-review]]. Human security review and network/storage
integration remain prerequisites to a deployed payment service.
