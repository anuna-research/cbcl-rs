---
id: SPEC-021
title: Validator Signing Budgets — Executable and Lean Models
version: 0.2.0
status: asynchronous-safety-refuted
last-updated: 2026-10-30
---

# Validator Signing Budgets — Executable and Lean Models

## Orientation

**The asynchronous safety claim is refuted.**
[[SPEC-021-validator-budget-model#BUG-2100]] gives a valid schedule finalizing 33
rights from 30. The partial version-renewal rule cannot refine a funded-payment
specification. Fixed-checkpoint and local-accounting theorems remain valid; their
premises do not establish the missing asynchronous invariant. Rejecting negative
updates or merely acknowledging a version by quorum is insufficient. The model is retained as the regression subject, not promoted as a
safe certification implementation.
[[SPEC-021-validator-budget-model#CON-2102]] records the repair gate.

This models the budget candidate selected for investigation in
[[SPEC-020-resource-certification#ADR-2002]]. It does not enable a certification
runtime. The failure is overspending through different witness quorums and partial capacity
renewal without a complete treatment of outstanding old-version certificates.
Even retained reservations do not prevent the demonstrated failure.

A pinned roster has n=3f+1 witnesses and quorum q=2f+1, with at most f Byzantine.
Each honest witness starts with a conservative fraction of the account's rights
and optional headroom. Signing an operation durably reserves its consumption.
All effects of the operation share one certificate. Its effects become spendable
only with quorum execution evidence. Owner-signed version requests reference
finalized funding and retain reservations for omitted signed operations.

The executable model uses exact scaled integer arithmetic and symbolic authenticated
identities. It exercises independently advancing witness versions and divergent
version merges. Its no-commit recovery path models a quorum fence plus an abstract
unique consensus decision; it does not implement consensus or its liveness.

Lean proves the finite signing-capacity argument, applies it to both budget
dimensions, proves local reservation/reconciliation identities, and proves that
quorum finality and a no-commit fence cannot coexist under honest-witness discipline.
The executable trace exploration is separate evidence. No theorem equating the
Python lifecycle with the Lean model or the eventual Rust runtime is claimed.

Controls: pinned context; distinct roster identities; source/issuer authorization;
positive amounts; exact integer budgets; atomic joint reservations; authenticated
funding receipts; replay exclusion; monotonic recognized history; retained omitted
reservations; final-effects threshold; persistent execution fences; bounded-buffer
funding admission; explicit assumptions and proof limits.

Readers evaluating safety follow [[SPEC-021-validator-budget-model#CON-2100]] and
[[SPEC-021-validator-budget-model#CON-2101]]. Implementers follow contracts to
[[SPEC-021-validator-budget-model#TEST-2100]] and
[[SPEC-021-validator-budget-model#TEST-2101]]. The maintainer owns the remaining
refinement and transport work in [[SPEC-021-validator-budget-model#Open work]].

## Amendment Channels

The maintainer's task instruction authorizes this model. Tier 1 independent
cross-model review checks the specification and deliverables. Human security review
remains necessary before production release. Changes cannot erase the distinction
between a formal model theorem, finite trace evidence and a deployed protocol proof.

## ADR-2100: Separate executable lifecycle from the parametric safety core

Use Python stdlib for inspectable lifecycle traces and Lean Std for proofs. Reuse
[[SPEC-019-state-rules#CON-1909]] operation accounting and the existing
`LeanCbcl.BoundedCounter` arithmetic definitions. Avoid a new parser, crypto scheme
or production certificate API during modelling. Inputs are typed model events;
JSON output is evidence, not a wire contract.

Use the conservative signing-budget mechanism studied in
[Stingray, sections 4–6](https://arxiv.org/html/2501.06531v1). CBCL's adaptation
recognizes funding credits only after final effects evidence. This is a deliberate
conservative modelling choice; source-protocol progress claims do not automatically
transfer. The model covers equal-key concurrent devices, not different-key owners
of one logical account. It does not implement the alternative COD candidate.

## REQ-2100: Authentic atomic signing

A model operation SHALL bind genesis, account, version, kind, amount and recipient.
An honest witness SHALL check source and issuer authority and reserve all required
budget dimensions atomically before recording its vote. A retry SHALL NOT charge
again. Invalid context, nonpositive amounts, unknown members and forged honest votes
SHALL NOT enter certificates. Faulty witnesses can endorse arbitrarily, but cannot
forge honest votes. Trace: [[SPEC-021-validator-budget-model#TEST-2100]].

## REQ-2101: Version reconciliation preserves exposure

Each witness SHALL track its own version and recognized finalized receipts.
A version request SHALL extend parent histories and apply each new receipt once.
Omitted signed operations SHALL remain charged. Certified transactions arriving
late SHALL retain their identity and dependencies. Divergent versions MAY merge
when the witness's current version is one of the parents. A merge SHALL NOT
reintroduce recognized credits or reclaim the same reservation twice.
Trace: [[SPEC-021-validator-budget-model#TEST-2100]].

## REQ-2102: Finality and recovery

Certification, local execution and finality SHALL remain separate stages.
Finality requires q authenticated effects votes. A no-commit voter SHALL persist
a fence before returning its vote, and an honest fenced witness SHALL NOT execute
a subsequently delivered old-version certificate. An honest witness that already
executed the affected version SHALL NOT issue a no-commit vote. A quorum fence
can authorize provisional rollback only through an abstract unique consensus
choice. Finalized receipts SHALL NOT be revoked or credited twice.
Trace: [[SPEC-021-validator-budget-model#TEST-2100]],
[[SPEC-021-validator-budget-model#TEST-2101]].

## REQ-2103: Nonvacuous evidence

The executable checks SHALL include successful mint/burn/pay/headroom traces,
concurrent same-account operations, malicious split quorums, withheld signatures,
late dependencies, replay, omitted reservations, version forks/merges and recovery
races. Negative cases SHALL demonstrate prohibited actions or unsafe mutations.
Lean theorems SHALL state their premises and contain no new axiom, sorry, admit,
or proof by native execution.
Trace: [[SPEC-021-validator-budget-model#TEST-2100]],
[[SPEC-021-validator-budget-model#TEST-2101]].

## CON-2100: Executable reference transition model

A genesis fixes initial rights, optional headroom, issuers, accounts and a committee.
The model scales all witness budgets by s=2f+1; k=f+1. Initial local budgets are
k times the account allocations; a signature consumes s times the operation cost.
No rounding is required. A positive cost needs that full scaled budget.

A version stores its account, parents and the union of parent recognized receipts
plus newly included finalized receipts. For each new receipt with delta d and
own reserved consumption c, a witness changes local budget by k*d+s*c. Signed
operations outside the recognized history keep their reservation. Budgets can be
negative after reconciliation; they represent outstanding exposure and SHALL NOT
be clamped or discarded. A witness with insufficient budget cannot sign new costs.

An operation's source budget costs are: burn/pay consume rights; capped mint and
headroom transfer consume headroom. Mint creates rights; capped burn creates
headroom; transfers create a matching recipient credit only after finality. An
uncapped mint still requires issuer authorization. No speculative netting of
unfinalized mint/burn can fund a signature.

The network adapter presents complete symbolic operations and certificates.
Each witness buffers missing executed dependencies. A ready dependency bypasses
pending-capacity refusal, then drains pending operations. Finalization records one
receipt after q distinct execution votes. The model's invariant checker observes
resource results; global balances are not a hidden signature-admission oracle.

Recovery models only the no-commit branch. Correct fence voters stop executing that
account/version. An abstract single consensus outcome installs cancellation evidence;
provisional execution can be removed and old reservations released under the fence.
The oracle's uniqueness and eventual decision are assumptions, not Python properties
of a distributed consensus algorithm. The commit/adopt branch, adaptive corruption,
Byzantine payload availability and real crash persistence need later refinements.

## CON-2101: Lean proof boundary

The Lean model SHALL expose definitions and proofs for:

- Sum-of-signature capacity: each certificate's charge occurs at enough honest
  witnesses, and each honest witness's total charge is bounded. Double counting
  yields total certified consumption at most the initial resource budget.
- The argument for both rights and headroom, with positivity for cancellation of
  the scale factors. The honest-core interpretation and certificate coverage are
  explicit; numeric budget sufficiency is not assumed as the conclusion.
- Local signing reservation accounting and reconciliation that reclaims only
  covered own reservations, with omitted exposure retained.
- Quorum effects versus no-commit fences: honest witnesses cannot contribute to
  both; with n=3f+1 and at most f faulty, both quorums cannot exist.
- Final receipts as a monotonic abstraction; internal bookkeeping can stutter.

These prove the abstract safety core, not asynchronous global-version safety,
network liveness, complete FastUnlock, crash-durable storage, cryptographic key
binding, a joint-budget Rust refinement or arbitrary contract effects.

## TEST-2100: Lifecycle scenarios and adversarial schedules (core)

Run the Python lifecycle model and its tests. Replay generated evidence. Include
successful resource transitions plus failed attacks and assertions on unchanged
state. Exhaustively vary small signature assignments and selected delivery orders.
Mutate omitted-reservation retention, replay protection, effects threshold and
fence enforcement separately; each mutation needs a failing behavioral assertion.
Record the exact finite scope; sampled or selected traces are not exhaustive proof.

## TEST-2101: Lean build and axiom audit (core)

Compile the new module with the repository's Lean toolchain, import it into
`LeanCbcl.lean`, and include the public safety theorems in the axiom audit.
Run the existing proof linter. Check positive and negative concrete examples.
A mutation of a load-bearing numerical bound must make a relevant example or
proof fail. Print theorem dependencies; no custom axiom or sorryAx is allowed.

## BUG-2100: Partial version renewal permits finalized overspending

Status: reproduced and formally refuted. Severity: safety-critical for the proposed
certification model. The implemented host-gated escrow primitive is not changed.
Trace: [[SPEC-021-validator-budget-model#REQ-2104]],
[[SPEC-021-validator-budget-model#TEST-2102]].

The committee has four witnesses, only witness 3 Byzantine. The source has 30 rights;
all honest witnesses start with 60 scaled signing units. All payments go to the same
recipient. A, B and C each spend 10 and have distinct nonces.

| Act | Signing witnesses | Finalized before renewal? |
|---|---|---|
| A: pay 10 | 0, 1, 3 | No |
| B: pay 10 | 0, 2, 3 | No |
| C: pay 10 | 1, 2, 3 | Yes |

After signing, honest free budgets are [0,0,0]. A new version includes only C. Local
reservation accounting correctly produces [-20,10,10]; no omitted reservation is
forgotten. Witnesses 1 and 2, together with witness 3, then certify new-version
payment D for 3 units, charging 9 scaled units each. C is D's executed dependency.
D finalizes, then the delayed old certificates A and B finalize. The recipient has
33 rights and the source has -3. Every payment has three signing votes and three
honest execution votes. The model's diagnostic assertion detects the violation
after the final effects threshold is met; it is not a resource-admission guard.

The variant where witness 0 refuses renewal still fails. Witnesses 1,2,3 adopt the
new version; all honest budgets remain nonnegative, yet D and the delayed payments
finalize identically. Refusing negative budgets, clipping the negative budget, or
merely obtaining quorum version acknowledgments cannot repair this trace.

The old fixed-checkpoint theorem is not contradicted. Cumulative charges at witnesses
1 and 2 become 69 rather than their original capacity 60. Its witness-capacity
premise therefore does not hold across this version change. The local reconciliation
identity remains true, which shows why that identity alone cannot justify refinement.

This finding concerns our executable adaptation. No conclusion about the complete
external Stingray protocol is claimed. The Lean payment fragment is independently
audited against the relevant Python guards; no cross-language extraction theorem
is assumed or asserted.

## REQ-2104: Global finalized resource safety

Every reachable finalized history SHALL preserve nonnegative rights for each
account and nonnegative headroom when capped. Final receipts SHALL correspond to
legal funded business transitions under the finalized-balance observation.
The current version-renewal model does not satisfy this requirement.
Trace: [[SPEC-021-validator-budget-model#BUG-2100]],
[[SPEC-021-validator-budget-model#TEST-2102]].

## CON-2102: Repair gate — sealed, authenticated checkpoint cuts

Status: design obligations, not an accepted repair protocol or implemented API.
Owner: CBCL maintainer. Runtime work remains gated by this design and its proof.

Before signing capacity is renewed, the checkpoint needs verifiable treatment of
every old operation that is final or could still become final. Such an operation
must remain accounted for in the renewed capacity, or evidence must establish
that it can no longer obtain final effects. Stopping new old-version signatures
alone is insufficient because existing signing certificates survive.

A candidate design seals the old epoch through durable witness promises, collects
relevant signed/executed evidence, and notarizes a complete, consistent cut. It
preserves already finalized operations, carries unresolved consumption explicitly,
and makes any cancellations enforceable at the effects boundary. A partial-commit
cut needs an included-operation rule; the existing whole-version no-commit branch
cannot simply cancel a version in which C already finalized.

Competing cuts require a consistency argument over the same genesis/account/epoch.
The cut must be recognized from local authenticated evidence and certificates, not
a hidden global balance oracle. Restarts retain sealing promises, reservations and
effects evidence. Both budget dimensions, cross-account funding and delayed old
certificates remain part of the proof obligations. Timeout alone cannot reset them.

The next task specifies this protocol and its precise activation/finality contract,
then proves that its local transition rules imply the required cut property. A new
refinement proof cannot assume the cut's resource-safety conclusion as a premise.

## TEST-2102: Executable and Lean asynchronous refutation

Run `python3 proofs/validator-budget/async_counterexample.py` with no mutation flag.
It SHALL reproduce both the all-update trace and the nonnegative-adopter variant.
A successful command means the refutation reproduced, not that the model is safe.
The evidence explicitly reports initial 30, finalized 33 and final source -3.

`LeanCbcl.ValidatorBudgetRefutation` recognizes the guarded payment-only traces.
`guarded_trace` and `nonnegative_adopters_trace` SHALL establish that every command
returns success, ruling out a default final state masking a rejected step.
`final_quorums` and `overspent` establish the actual certified, finalized violation.
`no_funded_refinement` SHALL exclude that endpoint from an independently defined
funded-payment business specification under the intended balance observation.
The repository build and axiom audit SHALL include these theorems.

Independent review checks all active guard correspondences: source/context
constants, positive amounts, headroom's zero-cost guard, roster membership, parent
version, finalized coverage, executed dependencies, distinct signing/effects votes,
and the absence of recovery or cancellation. The finite counterexample refutes
universal safety; it does not need an exhaustive network search.

## Open work

Owner: CBCL maintainer. Specify the sealed-cut repair in
[[SPEC-021-validator-budget-model#CON-2102]], amend the executable transition
rules, and then prove refinement of the amended model. The current model's safety
claim is refuted, so it cannot be discharged by stronger bookkeeping lemmas.
Account for delayed certificates, partial commits, competing cuts, both budgets
and cross-account funding before selecting a production protocol. The broader
[[SPEC-020-resource-certification#TEST-2006]] gate remains incomplete.

## Evidence

[[validator-budget-model]] records the executable checks, isolated mutations, Lean
build, axiom audit and independent review. The model is available and its asynchronous resource safety is refuted. Repair,
refinement and runtime obligations in [[SPEC-021-validator-budget-model#Open work]]
remain open.

## Changelog

- 0.2.0 (2026-10-30): refute partial version renewal with executable and Lean
  counterexamples; add explicit global safety requirement and sealed-cut repair gate.
- 0.1.0 (2026-10-30): executable dual-budget reference lifecycle and Lean
  signing-capacity/finality core, with explicit scope and remaining refinement.
