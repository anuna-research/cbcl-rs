---
id: SPEC-020
title: Resource Agreement — Certification and Compatible Sets
version: 0.3.1
status: design-recommendation
last-updated: 2026-10-30
---

# Resource Agreement — Certification and Compatible Sets

## Orientation

The bounded counter is implemented; malicious-owner certification is not.
Its current verifier faults on an account fork and requires a correct host issuance
gate. A richer profile needs durable monetary finality even when owners equivocate,
and should eventually support compatible concurrent operations from one account.

Decision: retain the arithmetic/language kernel and separate authenticated evidence,
agreement and spendable finalization. Prefer invariant-aware account-local
certification. Compare CryptoConcurrency-style compatible sets with Stingray-style
validator signing budgets before choosing a runtime contract. Ordinary BGLA over evidence
is insufficient: two payments of 80 each against 100 can both enter comparable
evidence while remaining jointly unaffordable. Self-healing after conflicting
receipts does not restore spent funds. Fixed-slot certification remains a simpler
sequential baseline; split votes can stall it even for compatible payments.

Controls: immutable authenticated genesis; distinct canonical witnesses; certified
funding provenance; atomic rights/headroom decisions; durable acceptance/closure;
monotonic receipts; version-history safety; dependency delivery despite full buffers.
These are design obligations. No agreement or certification runtime is implemented.

The current owner-chain verifier cannot accept compatible siblings unchanged.
[[SPEC-020-resource-certification#ADR-2001]] explains that compatibility boundary
and the source assumptions. [[SPEC-020-resource-certification#TEST-2005]] gives
runnable finite counterexamples. [[SPEC-020-resource-certification#TEST-2006]] is the
next modelling task and gates richer-profile runtime work. The fixed-slot candidate
in [[SPEC-020-resource-certification#ADR-2000]] and its contracts remains a draft
baseline, not the selected production implementation.

Reviewers follow the decision and source findings. Implementers follow the next
model's acceptance criteria. Dialect authors keep the existing bounded-counter
syntax; future bookkeeping/profile compatibility requires an explicit decision.

## Amendment Channels

The maintainer can amend this prototype through repository review or an explicit
task instruction. No amendment can describe a signature quorum as a proof of
application validity or erase the durable-acceptance and authenticated-genesis premises.
Tier 1: independent cross-model review is required; human security review remains
a release obligation before operating a deployed payment service.

## ADR-2001: Prefer invariant-aware account agreement; retain fixed slots as a baseline

Status: accepted research direction; runtime selection remains gated by the model.
Owner: CBCL maintainer. Source: explicit user request to compare BGLA before coding.
Trace: [[SPEC-019-state-rules#ADR-1915]], [[SPEC-020-resource-certification#TEST-2005]].

Decision: keep the bounded-counter language and arithmetic kernel. Target
account-local invariant-aware certification for the richer profile. Compatible
operation sets are one candidate; validator signing budgets are another, as
[[SPEC-020-resource-certification#ADR-2002]] records. Retain
[[SPEC-020-resource-certification#ADR-2000]] as a restricted sequential baseline.
Do not implement global BGLA over raw acts as a substitute for resource validity.
Do not introduce a generic interchangeable agreement trait before the candidate
profiles have precise evidence and finalization contracts.

The preferred direction is a protocol family, not a claim that COD or Stingray
directly runs CBCL. The next implementer models the dual-budget acceptance and closure boundary
in [[SPEC-020-resource-certification#TEST-2006]] before writing a certification
runtime. Existing escrow behavior stays enabled under its documented host premise;
no certification profile is enabled by this decision.

### Named failure modes

- BUG-2000, invalid join: individually affordable debits can overspend after union.
  The same failure applies to concurrent consumption of increment headroom.
- BUG-2001, honest-device stall: compatible sibling operations still fork the
  current account chain and can split fixed-slot witness votes permanently.
- BUG-2002, quorum subset gap: different quorums can certify different individual
  debits although each honest replica's local aggregate stays within its budget.
- BUG-2003, irreversible recovery: discovering a bad quorum after two receipts
  were spent does not restore the violated monetary bound.
- BUG-2004, retracting selection: deterministic hash-order filtering of growing
  evidence can displace an earlier accepted payment when new evidence arrives.

### Source findings

[BGLA, sections 3, 5–7](https://arxiv.org/pdf/1910.05768) supplies validity,
comparability and progress for a join semilattice under authenticated reliable
asynchronous channels and n≥3f+1 participants. Its replicated-state-machine
construction uses commutative updates. WTS includes reliable value disclosure
and safe-value checks before ACK/NACK refinement; a signature quorum alone is not
that protocol. The relevant point is agreement on comparable values, not selection
of one universal operation order. These findings do not establish that valid
bounded-counter histories form the required semilattice.

[CryptoConcurrency, sections 6–8 and appendix A](https://arxiv.org/pdf/2212.04895)
adds account-specific Closable Overspending Detectors. Prepare seeks matching
whole debit sets with certified credits; Accept protects recoverability. Close
preserves accepted debits and yields a snapshot. Account-local consensus, trusted only by the owners, proposes a next-epoch state.
Replicas validate and quorum-notarize it, signing at most one result per epoch.
Other accounts do not need to trust the owners' consensus implementation. Success
conditions concern correct accounts and nonoverspending submitted subsets, not
an unconditional promise that eventually arriving funds make every request succeed.
The protocol protects against malicious-account overspending, while progress for
malicious owners is a separate matter. This is a stronger fit for concurrent
wallets than ordinary BGLA, but it does not prove CBCL's dual-budget extension.

[Self-healing lattice agreement, sections 2–3](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.OPODIS.2021.25)
combines object and configuration lattices, forward-secure signatures, accusations
and reconfiguration. Its long-lived construction assumes benign clients; the
one-shot appendix separately discusses Byzantine clients. Its accountable contract
allows incomparable learned values followed by new provable accusations. Liveness
assumes configuration availability and finitely many reconfigurations; this is
not the fixed-roster BGLA safety contract with a different fault threshold.
Accountability and later state merging therefore do not substitute for never
issuing conflicting spendable receipts. These are useful recovery ideas only after
an explicit monetary-finality argument.

AT2 and Astro findings and source links remain in
[[SPEC-019-state-rules#Certification research — AT2-style asset transfer]].

### Comparison against CBCL requirements

The following assessments are design inferences from the sources and current code.

| Candidate | Malicious-source safety mechanism | Concurrent writers | Recovery | Fit with current runtime |
|---|---|---|---|---|
| Fixed-slot ACK/COMMIT | Honest quorum intersects a durable vote-once slot | One sequential writer; compatible siblings still compete | No winner after split votes; no timeout unlock | Closest: preserves owner chain, but certified-history layer is missing |
| Ordinary BGLA on raw evidence | Comparable growing evidence; no counter invariant by itself | Can include both conflicting spends | Protocol progress does not make an invalid join spendable | Not a resource-finalization replacement |
| Account-local invariant-aware sets | Whole-set acceptance plus certified funding and recoverable closure | Target: compatible same-account operations coexist | Close plus account-local consensus under its stated progress assumptions | Preferred richer direction; needs new history interpretation and dual-budget proof |
| Self-healing accountable agreement | Evidence identifies inconsistent decisions and faulty signers | Depends on chosen object and client assumptions | Certified reconfiguration and merging | Later accountability/reconfiguration work; not sufficient monetary finality |

Independent accounts already operate concurrently under escrow allocations.
A single global BGLA instance would add cross-account coupling without solving
shared-budget contention. There is no demonstrated requirement for that coupling.

### Which lattice, and which invariant?

Let E be authenticated proposals and evidence, ordered by set inclusion. Union
is a valid join for this evidence store. Let F be finalized resource operations.
The invariant belongs to F, not to every element of E. Authentication alone does
not establish membership in F. Agreement decisions over E can still contain
financially conflicting proposals.

For balance 100, sets {pay Bob 80} and {pay Carol 80} are individually affordable.
Their union is not. Replacing balance with headroom gives the ceiling counterexample.
Adding an absorbing fault element can complete an abstract lattice, but that
element is not a spendable state and supplies no finality/recovery policy.

Pairwise compatibility is insufficient: with funds 2, three distinct unit debits
fit in every pair but not together. Quorum signatures on individual membership
also fail. With witnesses {0,1,2,3}, witness 3 Byzantine and quorum 3, certificates
A={0,1,3}, B={0,2,3}, C={1,2,3} certify three debits. Each honest witness endorsed
only two. Whole-set signing with monotonic acceptor state prevents this particular
gap. Conservative witness signing budgets are another candidate defense. Neither
finite mechanism alone supplies a complete live agreement protocol.

At a pinned account checkpoint, necessary accounting conditions are:

```text
R = R0 + committed mint + rights-in - burn - rights-out >= 0
H = H0 + committed burn + headroom-in - mint - headroom-out >= 0
```

H is present only for a ceiling. These are accounting equations, not a sufficient
acceptance rule. Each credit needs authenticated provenance and idempotent identity;
its creating operation must already be committed under the relevant rule. Both
budgets and all effects of one operation require one atomic acceptance decision.
Do not independently certify different sets for each budget and then combine them.
A net-zero mint/burn cycle is not evidence of initial funding: at floor=ceiling,
no positive mint or burn is initially enabled despite cancelling net deltas.
The new model must preserve this causal funding distinction.

### Compatibility with implemented CBCL

The current `escrow::observe` stores at most one successor per (signer, previous).
A second successor faults the history before aggregate affordability is evaluated.
The binder emits one `:escrow-prev` and explicit `:escrow-deps`. The source account
is the authenticated signer. These are semantic constraints, not certificate
serialization details.

Concurrent devices using one signing identity need a new certified account-history
interpretation if compatible siblings are to coexist. A shared logical account
controlled by different signing identities additionally needs an authorization and
account-identity design; current signer=account semantics do not provide it.
Neither change can be silently activated by swapping a certificate verifier.

A candidate shared-account representation is an account/epoch checkpoint followed
by certified cumulative operation sets, carrying the previous checkpoint and
certified funding closure. Each commit preserves earlier accepted operations.
Closure accounts for all issued acceptance evidence before the next epoch starts.
This sketches the model to evaluate, not a new wire grammar or a verified CBCL
adaptation. Existing operation addresses remain the identifiers; certificate
identifiers cannot replace them. A versioned host profile pins its interpreter.
Unchanged business verbs are a goal; compatibility of compiler-owned bookkeeping
must be established rather than assumed.

### Stuttering refinement boundary

The proposed abstraction maps implementation state to F and its resource snapshot.
Evidence receipt, retry and ACK refinement can leave that abstraction unchanged.
Finalization changes F only by a legal, dependency-closed extension. A proof needs
both transition preservation and progress; permitting infinite stuttering alone
proves no liveness. Full BGLA properties are not reduced to a stuttering step.
Whether this mapping works for concurrent certified batches is part of
[[SPEC-020-resource-certification#TEST-2006]], not an implemented theorem.

### Baseline review findings to preserve

Any bounded implementation needs a path for a ready funding certificate when its
pending buffer is full. Otherwise one pending spend can block its own dependency
forever. Evaluate an incoming-ready bypass before pending-capacity refusal.
History exhaustion remains explicit backpressure, not a claim of unbounded progress.

The fixed-slot candidate only represents root, opener and resource operations.
Restrict its supported protocols to that predecessor closure until a non-resource
admission contract exists. This restriction needs an installation check and a
negative test before the baseline is called implemented.

## ADR-2002: Compare validator signing budgets before selecting the runtime

Status: accepted research priority, following the additional literature search.
Owner: CBCL maintainer. Trace: [[SPEC-020-resource-certification#ADR-2001]],
[[SPEC-020-resource-certification#TEST-2007]], [[SPEC-020-resource-certification#TEST-2008]].

The source findings and candidate trade-offs are in
[[byzantine-resource-literature]]. Do not treat whole-set agreement as the only
safe alternative to fixed slots. Model conservative validator budgets first, then
compare their availability and lifecycle costs with compatible sets. Do not combine
unproved pieces from the protocols into a purportedly verified hybrid.
The existing per-account escrow allocation is not a validator signing budget.
These need distinct state, identity, persistence and authority contracts.

Ordinary BGLA remains useful for comparable monotonic evidence. It is not selected
as a universal runtime for every state rule. Invariant-confluence analysis supplies
a way to classify what needs resource agreement; a compiler-based checker is a
future idea, not a new authoring obligation or implemented analysis.

## TEST-2005: Agreement comparison evidence (core)

Trace: [[SPEC-020-resource-certification#ADR-2001]].
Run `python3 proofs/bounded-counter-certification/compare_agreement.py` and compare
its JSON with `outputs/bounded-counter-agreement-comparison.json`. The assertions
exercise both non-join-closed budgets, the per-operation-quorum counterexample,
whole-set monotonic signing in a finite fixed-budget model, pairwise insufficiency,
nonmonotonic hash filtering and the unfunded net-zero cycle. Run the existing
`funding_evidence_pending_replay_and_forks` Rust test to corroborate current fork
semantics. Neither harness implements BGLA, COD, signatures or network liveness.

Independent review checks the source assumptions, inference boundaries and next
implementation task. Review evidence lives in [[bounded-counter-agreement-review]].

## TEST-2006: Next executable model (depth; prerequisite to richer-profile runtime)

Owner: CBCL maintainer. Compare separate compatible-set and conservative-budget
models under one pinned roster. Both need certified credit provenance and joint
rights/headroom transitions. The compatible-set model includes complete-set
certificates and accept/close races. The budget model includes outstanding
reservations across owner-signed version updates referencing certified transactions,
replay, rounding and version merges. Treat each candidate's activation and recovery rules separately.
For the budget candidate, distinguish certification, execution and finality using
quorum effects evidence or a proved equivalent criterion. Local execution is not
a spendable receipt. Exercise FastUnlock racing a certificate or local execution
and preserve finalized effects while allowing the source protocol's provisional
execution to be undone. Acceptance requires preservation of
all earlier final receipts; conflicting sets cannot both become spendable; duplicate
credits cannot increase capacity; neither budget goes negative; stale state cannot
authorize new uncovered consumption; and bounded buffering does not block needed funding.

Exercise equal-key concurrent devices first. Separate-key shared accounts require
the account authorization decision described above. Do not declare this model
complete from the fixed-budget examples in [[SPEC-020-resource-certification#TEST-2005]].
For the compatible-set candidate, model malicious owners presenting divergent,
individually valid next-epoch snapshots. Owner-local consensus is not a trusted
safety oracle for these owners.
Replicas need a durable, unique next-state authorization per (genesis, account,
epoch), after validating the closure certificate, or a proved equivalent rule.
At most one such COD next-epoch state can activate; earlier accepted operations
remain covered. This is not a universal single-version rule for the budget model.
Stingray permits divergent versions followed by safe merges. Its model needs
reservation accounting over version histories rather than invented quorum-notarized
version updates. Model delayed old-version certificates and omitted signed
reservations, rather than resetting budgets from only the visible committed balance.

Progress evidence needs an explicit adversary/scheduler model and fallback consensus
assumptions, including whatever synchrony or randomization its implementation needs.
Either source protocol's safety argument needs an extension to two coupled budgets
before it justifies mint, burn or headroom transfer. Record usable capacity, stalls,
resynchronization work and certificate requirements alongside safety outcomes.

The selected validator-budget model is recorded in
[[SPEC-021-validator-budget-model]]. It supplies executable lifecycle evidence and
a Lean safety core, not completion of this broader comparison/refinement gate.

## TEST-2007: Additional literature evidence (core)

Trace: [[SPEC-020-resource-certification#ADR-2002]].
Crawl primary sources with ar-crawl and retain URL, timestamp, content digest and
local evidence path. Inspect actual protocol details for promoted candidates.
Record assumptions, CBCL adaptation gaps and next actions in
[[byzantine-resource-literature]]. Validate the reasoning independently and export
the sourced Elephant task graph. Abstract-only screened papers remain labelled.

## TEST-2008: Finite validator-budget comparison (core)

Trace: [[SPEC-020-resource-certification#ADR-2002]].
Run `python3 proofs/bounded-counter-certification/check_signing_budgets.py` and
compare its output with `outputs/bounded-counter-signing-budget-checks.json`.
Enumerate the n=4/f=1 unit-debit signatures in one version. Verify conservative
budgets prevent overspending in those cases, reproduce failure with full local
budgets, and record withholding and integer-dust limitations. A deliberate budget
mutation must make the safety assertion fail. This does not model dynamic funding,
version updates, reconfiguration, real signatures or network progress.

## ADR-2000: ACK/COMMIT with complete certified history

Status: draft sequential baseline, superseded as the preferred richer-profile
direction by [[SPEC-020-resource-certification#ADR-2001]]. The following contracts
are candidate obligations, not implemented API claims.
Trace: [[SPEC-019-state-rules#ADR-1915]].

Use fixed n=3f+1 canonical witness identities, q=2f+1. A prepare is an owner-signed
statement containing the pinned genesis, owner, positive sequence, escrow previous,
existing act address and complete wrapped-message commitment. A witness reserves
that exact statement atomically in a host durable journal before signing its ACK.
A commit carries the prepare payload and q distinct valid ACKs. ACKs establish
consistent selection, not a valid debit.

The profile follows the signed-ACK/commit approach discussed by AT2 and Astro,
with an explicit full-history relay interface. Every recipient retains and exports
the certified resource history, including complete payloads. The host delivers
and retries that history over reliable authenticated links. A receiver that lacks
a dependency buffers the commit and requests/retrieves the missing certified act.
This prototype does not implement Astro II's separate f+1 CREDIT protocol or
claim network totality from signature counting. Host scheduling and eventual
payload delivery are explicit progress premises.

Composition-first: reuse canonical S-expressions, SHA-256, [[SPEC-015-evidence-widening-v2#REQ-708|canonical key identity]],
R4's Signer capability, R5/R6 projection verification, the intent binder and the
existing dual-budget escrow verifier. New pure code supplies statement binding,
quorum recognition, witness reservation ordering and a certified-history boundary.
No network driver, new coin verb, VRF, parser or second act-address scheme is needed.
The genesis digest is a configuration identifier; acts keep existing addresses.

[CryptoConcurrency](https://arxiv.org/pdf/2212.04895) permits concurrent accesses
that jointly fit the balance and uses account-local consensus for contention.
That protocol is outside this sequential-account profile. Its concurrency and
recovery properties do not follow from our one-vote-per-slot journal.

## REQ-2000: Immutable authenticated context

The profile SHALL pin the installed dialect, thread, field, exact cast-bearing
root and opener, roster, fault bound and resource limits into one genesis digest.
The caller SHALL supply a trusted authenticated root and opener, not untrusted
proposals. The constructor SHALL rebuild act metadata and validate the initial
resource state and role/protocol structure. Account aliases mapping to the same
canonical key SHALL NOT create separate accounts. Witness resolution SHALL map
canonical identifiers injectively to actual verification keys.
Trace: [[SPEC-020-resource-certification#CON-2000]], [[SPEC-020-resource-certification#TEST-2000]].

## REQ-2001: Authentic proposals and certificates

The implementation SHALL recompute statements from actual messages. Owner
signatures SHALL bind the genesis and complete message; ACK signatures SHALL use
a distinct domain and bind the statement and canonical witness identity.
Malformed, unsupported-suite, duplicate, nonmember, forged, truncated and
cross-context certificate evidence SHALL be rejected before changing ledger state.
Trace: [[SPEC-020-resource-certification#CON-2000]], [[SPEC-020-resource-certification#TEST-2001]].

## REQ-2002: Durable account-slot vote exclusion

Before an ACK is returned, the host journal SHALL atomically persist the complete
statement keyed by genesis, owner and sequence. A retry of the identical statement
is idempotent. A competing statement, storage error or signing-key mismatch SHALL
return no ACK. The reservation survives restarts and is never unlocked by timeout.
All resource verbs, including headroom transfers, share that account lane.
Trace: [[SPEC-020-resource-certification#CON-2000]], [[SPEC-020-resource-certification#TEST-2002]].

## REQ-2003: Certified dependency-closed finalization

Only quorum-certified, owner-authenticated operations SHALL enter the delivery
buffer. An operation SHALL finalize only after its previous account position,
funding dependencies and protocol predecessors are finalized. Its sequence SHALL
be the next position and escrow previous SHALL match that owner's finalized tip.
Role/protocol and resource checks SHALL pass before adding the act. An invalid
certified act SHALL NOT debit balances or retract a receipt. Uncertified siblings
SHALL NOT enter resource observations. Missing dependencies remain pending. This baseline SHALL reject unsupported
profiles whose protocol predecessor closure requires non-resource intermediary acts.
Trace: [[SPEC-020-resource-certification#CON-2000]], [[SPEC-020-resource-certification#TEST-2003]].

## REQ-2004: Relay, replay and bounded progress

The ledger SHALL expose finalized acts read-only and export complete verified
certificates for relay/recovery. Replaying certificates SHALL NOT apply a debit
twice or emit a new finalization receipt. A drain SHALL revisit buffered operations
after funding arrives. A ready dependency SHALL have an admission path when the
pending buffer is full; pending capacity alone SHALL NOT refuse it. Buffer/history exhaustion SHALL return explicit backpressure
without corrupting finalized state. A fair host retries retained evidence after
backpressure and eventually delivers dependencies. A malicious owner or unavailable
host is not promised progress.
Trace: [[SPEC-020-resource-certification#CON-2000]], [[SPEC-020-resource-certification#TEST-2004]].

## CON-2000: Typed library boundary and purity map

The public API accepts typed Rust values, not an additional textual wire format.
The host first parses complete messages with the existing CBCL parser. External
transport adapters need their own bounded envelope recognizer before this API.
The statement preimage grammar is a canonical S-expression list of string atoms:

```text
statement = ("cbcl-resource-statement-v1" genesis owner sequence previous address message-digest)
owner-preimage = ("cbcl-resource-owner-v1" statement)
ack-preimage = ("cbcl-resource-ack-v1" canonical-witness statement)
sequence = positive u64 encoded as a decimal string
```

`Genesis::new` validates trusted bootstrap and freezes the configuration.
`Genesis::propose` constructs an unsigned proposal from a message; the owner signs
`Proposal::signing_bytes`. `acknowledge` checks owner authentication, persists the
vote through `VoteJournal`, then uses an R4 signer and verifies its output.
`Certificate` contains the proposal, owner signature and witness ACKs.
`Ledger::receive` verifies the complete certificate, inserts it into a bounded
buffer, drains valid dependency-closed operations and returns structured events.
Rejected and pending events identify the candidate address; finalized events are
the only application authorization notification. Host effects use that address
as an idempotency key after durable host retention of the certificate.

The pure kernel does not perform IO. `Keyring::verifier` resolves canonical keys
to R4 verifiers with an immutable injective key directory. `VoteJournal::reserve`
is the effectful persistence port. There is no accepting default keyring or journal.
A failed sign after persistence leaves the slot reserved; retry reuses its proposal.
The host pins genesis independently of incoming traffic. Restoring a ledger starts
from that same genesis and re-verifies retained certificates; raw acts cannot be
injected as finalized entries. Disabling this profile does not authorize spending
its balances through the raw verifier. Migration requires an explicit new design.

## TEST-2000: Bootstrap and context (core)

Construct a real dialect/root/opener; reject inconsistent act metadata, duplicate
key aliases, bad roster size, invalid initial allocations and changed context.
A changed genesis produces different signing bytes. Trace: [[SPEC-020-resource-certification#REQ-2000]].

## TEST-2001: Authentication and quorum (core)

Use real Ed25519 signatures. Accept a valid certificate; reject forged owner/ACK,
wrong context, missing ACKs, duplicate aliases, nonmember and unsupported suites.
Trace: [[SPEC-020-resource-certification#REQ-2001]].

## TEST-2002: Restart and competing proposals (core)

Persist an ACK reservation, reconstruct the witness over the journal, retry the
same proposal and reject a sibling. Storage failure returns no ACK. Split votes
stall one source while another source progresses. Trace: [[SPEC-020-resource-certification#REQ-2002]].

## TEST-2003: Coin and dual-budget finalization (core)

Run mint/pay/burn and capped headroom transfer. Deliver funded spends before their
credits; verify pending then finalization. Reject stale-parent and invalid certified
operations without balance changes. A late uncertified fork cannot retract a receipt.
Trace: [[SPEC-020-resource-certification#REQ-2003]].

## TEST-2004: Merge and replay (core)

Relay certificates to independent ledgers in differing orders; compare final
snapshots. Replay produces no duplicate receipts. Exercise buffer backpressure,
retained-evidence recovery and no_std compilation. Deliberately mutate quorum
and vote-order guards and require negative tests to fail.
Trace: [[SPEC-020-resource-certification#REQ-2004]].

## Open work

Owner: CBCL maintainer. Human security review, full protocol/Rust correspondence
proof, production journal and key-directory integration, authenticated transport
retention/retrieval and binding wire adapters are release depth. They do not gate
the typed library prototype, which exposes these as explicit host obligations.
Shared-account recovery, VRF selection, roster rotation and permissionless membership
require separate specifications. No deployable trustless service is claimed.

## Changelog

- 0.3.1 (2026-10-30): link the executable validator-budget model and Lean
  safety core, retaining the asynchronous refinement gate.
- 0.3.0 (2026-10-30): add Stingray, invariant-confluence and BEC literature;
  compare compatible sets with conservative validator signing budgets; require
  owner-independent next-epoch notarization in the model. No runtime change.
- 0.2.0 (2026-10-30): compare ordinary BGLA, invariant-aware account sets, fixed
  slots and accountable reconfiguration; select model-first richer-profile direction.
  Preserve reviewed fixed-slot candidate and its unresolved implementation obligations.
- 0.1.0: uncommitted fixed-slot prototype draft; no runtime implementation.
