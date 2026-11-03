---
id: SPEC-022
title: Sealed Checkpoints for Validator Budgets
version: 0.1.0
status: executable-prototype-partial-proof
last-updated: 2026-10-30
---

# Sealed Checkpoints for Validator Budgets

## Orientation

[[SPEC-021-validator-budget-model#BUG-2100]] refutes owner-supplied partial renewal.
This prototype replaces renewal with a sealed, authenticated checkpoint. The old
unsafe model stays intact as a regression subject. No production runtime is enabled.

Within an epoch, validators sign concurrently using fixed conservative allocations.
To renew, witnesses durably freeze their old signing journals and disclose candidate
operations. The checkpoint carries all disclosed candidates as obligations, including
uncertified candidates. A quorum certifies one successor checkpoint. New allocations
subtract cumulative obligations and add only distinct authenticated finalized credits.
Old certificates can still finalize: their consumption is already reserved.

For the 30-rights counterexample, every valid sealing quorum reveals A, B and C.
Reserving their full 30 leaves zero new rights, so D cannot certify. A checkpoint
containing only C is rejected. Nothing expires merely because a new epoch exists.

The Lean proof target is certificate coverage from honest frozen journals, unique
checkpoint choice, no repeated allocation on replay, and the accounting connection
between reserved old operations, fixed-epoch capacity and finalized balances.
Finite lifecycle tests and a proof/model correspondence argument remain distinct.
Do not describe individual lemmas as an extracted or complete distributed runtime.

Controls: pinned genesis/profile/parent; canonical witnesses; durable sealing before
report; frozen complete honest reports; authenticated candidate payloads; quorum
report verification; complete inclusion; vote-once successor; derived nonnegative
allocations; cumulative debit/credit sets; finalized credit evidence; fixed per-epoch
reservations; no bare version updates, cancellation or timeout release.

This first repair is deliberately conservative. Over-disclosed partial operations
can lock capacity. Competing successor proposals can split votes. Progress assumes
one coherent correct owner/driver proposes a complete candidate set within available
resources and fairly disseminates it. This is checkpoint progress only, and requires one coherent proposal presented
to honest voters, available payloads, and no competing solicitation that splits
votes. Correct ownership alone does not enforce a unique driver. Operation
progress additionally needs per-witness affordability: the conservative budget may
require splitting a large payment, even when the account balance can fund it. Malicious owners need not make progress.
No full WTS/GWTS or COD protocol is claimed; this is a model using monotonic evidence,
sealing and quorum exclusion. [[SPEC-022-sealed-budget-checkpoints#Open work]] owns
more permissive recovery and progress work.

Reviewers follow [[SPEC-022-sealed-budget-checkpoints#ADR-2200]]. Implementers follow
[[SPEC-022-sealed-budget-checkpoints#CON-2200]] to
[[SPEC-022-sealed-budget-checkpoints#TEST-2200]] and
[[SPEC-022-sealed-budget-checkpoints#TEST-2201]].

## Amendment Channels

The user authorized trying the sealed-checkpoint approach. Tier 1 independent
cross-model review and orientation comprehension apply. Human security review
remains a production-release condition, not a claim established by this model.

## ADR-2200: Fixed budgets, monotonic evidence and one certified successor

Retain fixed-epoch signing budgets and both resource dimensions. Replace every
bare renewal path. Candidate collection grows monotonically until a final checkpoint
statement is chosen. Witnesses vote once on that statement per parent epoch.
Reports and alternative quorum bundles are evidence sidecars; the statement identity
binds its semantic account/parent/debit/credit/allocation data, not a particular
choice of report bundle.

No cancellation is provided. A checkpoint conservatively reserves every included
candidate. An overloaded union stalls rather than arbitrarily discarding old rights.
For a correct owner, including all sent operations before soliciting checkpoint
votes avoids reliance on Byzantine participants contributing to a particular report
bundle. Same-key concurrent drivers still need a coherent closing proposal for
progress. Vote splitting does not license a timeout unlock.

## REQ-2200: Seal and disclose

Before returning a seal report, an honest witness SHALL persist a signing fence
for the account/epoch and an immutable snapshot of every operation it signed there.
No fresh signature for that epoch SHALL follow sealing; replay of an already
recorded signature is idempotent. A report SHALL bind genesis, account, epoch and
witness identity. Report retry SHALL return the same snapshot.
Trace: [[SPEC-022-sealed-budget-checkpoints#TEST-2200]],
[[SPEC-022-sealed-budget-checkpoints#TEST-2201]].

## REQ-2201: Complete and unique checkpoints

A proposal SHALL contain a quorum of authenticated, distinct seal reports for one
parent and include all candidates disclosed by those reports. Additional candidates
need owner authentication and the same parent epoch. An honest checkpoint voter
SHALL have sealed that epoch and SHALL require inclusion of its own entire report.
It SHALL durably endorse at most one successor statement per parent epoch.
A checkpoint SHALL require q distinct actual endorsements before installation.
Trace: [[SPEC-022-sealed-budget-checkpoints#TEST-2200]],
[[SPEC-022-sealed-budget-checkpoints#TEST-2201]].

## REQ-2202: Reserve cumulative obligations

The successor's charged set SHALL extend the parent's charged set with every new
candidate. Its credited set SHALL extend the parent's credited set only with
finalized, account-related receipts. Credits SHALL be counted once and use only
positive resource deltas; negative source deltas are represented by charged costs.
Both allocations SHALL be derived from those sets and genesis. Negative derived
allocations SHALL reject the proposal. No speculative credit or netting is allowed.
Trace: [[SPEC-022-sealed-budget-checkpoints#TEST-2200]],
[[SPEC-022-sealed-budget-checkpoints#TEST-2201]].

## REQ-2203: Independent installation and fixed-epoch signing

An honest witness SHALL install only a certified successor extending its current
account epoch, or idempotently replay that same successor. Installation SHALL create
one new budget journal keyed by epoch; it SHALL NOT reset a used journal.
Late old certificates SHALL remain valid and their finalization SHALL NOT refund
new capacity. Bare owner version updates and cancellation paths SHALL be unavailable.
Signing and finalization SHALL retain the existing authorization and effects checks.
Trace: [[SPEC-022-sealed-budget-checkpoints#TEST-2200]],
[[SPEC-022-sealed-budget-checkpoints#TEST-2201]].

## CON-2200: Typed prototype boundary

The executable model uses the existing symbolic authenticated operation model,
fixed roster n=3f+1 and quorum q=2f+1. It is a separate class/profile, not a patch
that makes the refutation disappear by changing its subject. There is no new wire
parser; typed reports and checkpoint proposals are recognized completely before
voting or installation.

A seal report is (profile/genesis, account, parent epoch, witness, signed candidates).
A checkpoint statement is (profile/genesis, account, parent epoch,
cumulative charged set, cumulative credited set, derived rights, optional headroom).
A proposal adds authenticated report evidence to that statement. Witness signatures
are symbolic journals, not cryptographic implementations.

For each resource dimension x:

```text
allocation_x = genesis_x
             + sum(positive finalized deltas in credited set)
             - sum(source costs in charged set)
```

The per-witness initial budget in that epoch is k*allocation_x, k=f+1; signatures
cost s*amount, s=2f+1. There are no within-epoch budget additions or refunds.

Genesis and every parent checkpoint are pinned and certified. Reports/candidate
payloads and finalized receipt proofs are available to the verifier. Global final
balances are diagnostic observations, not signature or checkpoint-admission oracles.
Old signing certificates are never silently invalidated by epoch advance.

## CON-2201: Formal proof obligations

For an honest epoch journal, prove by induction that sealing freezes its signed set
and its report contains every subsequent recorded vote. Combine that with quorum
intersection to prove every old certificate, including a later-assembled one,
is covered by any valid checkpoint. Do not assume coverage as the certificate's
meaning. Derive it from the voting and freezing rules.

Likewise derive unique successor certification from honest vote-once journals and
quorum intersection. The fixed-epoch capacity theorem must obtain witness capacity
from initial allocation and guarded fresh signing, not assume refreshed capacity.

Finally connect cumulative obligations and authenticated credited receipts to the
resource observation. For each dimension, past finalized consumption is included
in charged obligations, present-epoch certified consumption fits the remaining
allocation, and credited receipts are a subset of actual finalized credits.
This implies nonnegative finalized resources under those derived premises.
State precisely which premises are proved from transitions and which correspondence
with the executable implementation remains unproved.

## TEST-2200: Executable repaired-model evidence (core)

Replay the 33-from-30 schedule: partial checkpoint C fails; a complete A/B/C cut
leaves zero new rights; delayed A/B finalize safely. Exercise report omission,
nonmembers/duplicates/forgery, post-seal signing, cut forks, unsupported bare renewal,
wrong allocations, speculative and duplicate credits, old certificate relay,
replayed installation, asynchronous witness catch-up, capped mint/burn/headroom,
and conservative refusal of overloaded candidate unions.

Mutations omit report inclusion, permit post-seal signing, permit competing successor
votes, or count a credit twice. Targeted behavioral assertions must catch each.
No successful check claims a proof of arbitrary schedules or production persistence.

## TEST-2201: Lean build and independent proof review (core)

Compile the sealed-journal, quorum-coverage, unique-successor and accounting lemmas
with no custom axioms or proof holes. Include main-library imports and central axiom
audit entries. Add concrete positive/negative examples, including the refutation's
payment amounts, and deliberate load-bearing mutations. Review the proof boundary
and executable correspondence independently.

## Open work

Owner: CBCL maintainer. Full asynchronous lifecycle refinement/extraction,
Byzantine payload retention, crash-durable journal adapters, complete cancellation
and contention recovery, and stronger multi-driver progress need further work.
The existing counterexample stays a regression for the old model. No production
certification profile is enabled by these prototype artefacts.

## Evidence and remaining proof obligations

The executable prototype is `proofs/validator-budget/sealed_model.py`; its runner is
`check_sealed.py`. Recorded behavioral evidence is in
[archived sealed-budget-checks.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/sealed-budget-checks.json). The old unsafe model remains unchanged.
Independent review found and corrected exact-type recognition of checkpoint and
report fields (Python float/bool equality must not authenticate integer fields).

`LeanCbcl/SealedCheckpoint.lean` proves honest quorum intersection, guarded local
spending bounds by transition induction, frozen **spent totals**, and an accounting
inequality. Its unique-successor and late-certificate lemmas still assume the
shared voter/signer and report-completeness premises explicitly. The journal does
not yet model operation identities, complete report snapshots, checkpoint voting
or installation. Thus frozen totals do not establish signed-set completeness,
especially for zero-cost operations. The local capacity induction is not yet
connected to transaction-indexed quorum charges. Replay safety is tested in Python,
not established by a Lean installation transition. These are outstanding core
obligations of [[SPEC-022-sealed-budget-checkpoints#CON-2201]] and
[[SPEC-022-sealed-budget-checkpoints#TEST-2201]], before full asynchronous refinement.
No completion claim for those obligations is made.

An isolated Lean mutant removes the signing affordability premise; compilation
fails at the spending-bound proof, recorded in [archived sealed-budget-lean-mutation.json](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/sealed-budget-lean-mutation.json).
The complete library builds and the central axiom audit passes. Vault-wide zetl
validation still reports dead links; no vault-clean claim is made.

The Orientation-only reader correctly predicted late settlement, zero capacity
in the counterexample, conditional progress and the governing artefacts. Its
questions about quorum intersection, journal completeness and credit evidence
remain explicit model/proof boundaries above, rather than runtime guarantees.
