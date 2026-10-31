---
title: Independent consensus-free literature review
mode: explanation
reviewer: /root/consensusless_literature_review
date: 2026-10-31
status: review-evidence
---

# Independent consensus-free literature review

The reviewed literature does not reveal a necessary replacement for the safety
construction in [[SPEC-025-consensus-free-refinement]]. It does reveal missing
comparisons in [[byzantine-resource-literature]], particularly progress contracts,
history queries, private transfers and storage growth. This is a literature and
design-boundary review, not an independent verification of the Rust implementation
or Lean proofs. The CBCL maintainer owns the decisions and follow-up contracts.

## Essential boundaries before wiring

The existing specification already permits stalled checkpoints and execution/fence
splits. Rust integration can proceed within that scope. Its externally observable
contract must preserve these distinctions:

* An operation certificate is not an effects-finality certificate. SPEC-025 permits
  cancellation to prevent an operation certificate from ever finalizing. Labeling
  that first certificate “payment final” would import a property from another
  protocol that this model does not prove.
* A cached balance or received transaction set is a local observation. Complete
  sealed signing reports protect epoch accounting; they do not establish that a
  client has learned every finalized incoming or outgoing transaction. No complete
  account-history or globally current balance API follows from the ghost archive.
* Termination, reclaimability, and full-balance spendability are separate promises
  from conservation. Conservative budgets can leave funds temporarily unavailable;
  split votes can make this permanent. A coordinator may retry and relay, but
  cannot silently decide a conflicting checkpoint, reset a vote, or release a
  charge after a timeout.
* Immutable signed history and permanent fence/effects exclusion require durable
  state in any crash-recovering deployment. Storage limits may reject work or
  cause a declared stall; pruning cannot silently erase anti-replay or exclusion
  evidence. No paper below supplies a drop-in safe pruning theorem for SPEC-025.

These are checks on correspondence and public claims, not requests to add privacy,
permissionless membership, or complete-read services to the current implementation.
If the integration exposes only the typed safety core with these boundaries, no
literature finding here requires delaying it for a different consensus-free design.
If it advertises stronger behavior, the relevant contract and validation are
essential before exposing that behavior.

## The requested bibliography, checked against primary sources

The [requested section](https://github.com/hellas-ai/awesome-consensus#consensus-less--crdt-approaches)
is a useful discovery index, not a uniform list of Byzantine payment solutions.
Its entries have materially different fault models and progress requirements.

| Source | Exact takeaway and relevance |
|---|---|
| [QAAT, v2, sections 3–6 and appendix D](https://arxiv.org/html/2405.18072v2) | A genuine asynchronous consensus-free asset-transfer design: one process owns each account, quorum Agreement Proofs serialize that process's sequence, and correct invocations terminate. Balance reads expose the caller's local view. Receiver and amount privacy use commitments, accumulators and zero-knowledge proofs. **Version correction:** v2 states storage linear in the process's own transfers for a fixed security parameter; succinct proof sizes do not mean polylogarithmic total history storage. This is an alternative privacy/evidence representation, not a solution to same-account concurrent-owner contention. |
| [FastPay, sections 4–5](https://arxiv.org/pdf/2003.11506) | Per-account consistent broadcast, fixed Byzantine quorum assumptions, client-relayed certificates and disciplined sequential senders provide a concrete asynchronous progress baseline. A transfer certificate supports its payment-specific eventual execution guarantee. SPEC-025's cancellable operation certificate must not inherit that finality label. The standalone native-asset mode does not require the optional primary-chain bridge. |
| [Stingray, sections 4–6 and appendix A](https://arxiv.org/html/2501.06531v1) | Conservative signing budgets directly motivate the current design. The bounded-counter liveness proof assumes the specified owner algorithm, including version management. Collective version merges can recover some contention without consensus, but sustained contention invokes FastUnlock consensus. Full-balance exhaustion also needs the specified treatment of residual small balances. The whole system is not an unconditional no-consensus recovery solution. |
| [CryptoConcurrency, sections 5, 9–10 and appendix C](https://arxiv.org/pdf/2212.04895) | Shared-account recovery uses account-local consensus, so it cannot replace SPEC-025 under the user's constraint. Its separate account-transaction completeness property is valuable: the query contains committed transactions preceding invocation, supported by quorum append-only storage and read writeback. Such storage is evidence dissemination, not necessarily a balance-ordering authority. Its suggested occasional-consensus checkpointing must not be imported into CBCL. |
| [Process-Commutative Objects, sections 4–7](https://arxiv.org/html/2311.13936v2) | A genuine broader abstraction with per-process exclusive operations, FIFO reliable broadcast, legal-trace conditions, strong eventual consistency and pipeline consistency. The Byzantine construction assumes fewer than one third Byzantine participants and guarantees termination of correct-process operations. It includes money transfer, deletion rights and Petri-net examples. Useful for classifying authored CBCL rules, but the ownership and legality conditions require a proof; syntactic commutativity alone is insufficient. Concurrent devices sharing an identity do not automatically satisfy its one-process execution discipline. |
| [Making CRDTs Byzantine Fault Tolerant, sections 3–5](https://martin.kleppmann.com/papers/bft-crdt-papoc22.pdf) | Hash-linked operation histories, content-derived identifiers and deterministic dependency-context validity checks can preserve strong eventual consistency with arbitrarily many Byzantine participants. The construction stores delivered update history and still requires algorithm-specific validity arguments. Converging on the same malicious operation does not make spending it financially valid. This belongs in evidence replication, not in the bounded-resource authorization proof. |
| [Blocklace, v4, sections 2 and 4–6](https://arxiv.org/html/2402.08068v4) | A signed DAG supports operation/delta-state CRDT use and eventual exclusion of detectable Byzantine behavior, including equivocation under collusion. The model has a finite identity set; its finite-harm guarantee is not an operational memory bound or a monetary finality rule. Application interpretation and admissibility remain necessary. |
| [GOC-Ledger, abstract and sections 1–2](https://arxiv.org/pdf/2305.16976) | Its intended setting is trusted replicas with crash/recovery. Concurrent same-account updates can produce negative balances; strict nonnegativity requires an additional ordering mechanism. State-based convergence and grow-only summaries are useful ideas, but this is explicitly not a Byzantine overspending solution. Promoting it as a safer replacement would weaken the threat model. |
| [On Consensus Number 1 Objects, sections II–III](https://tik-db.ee.ethz.ch/file/4460f8739793dba75c212e40e0585a7f/Consensus_Number.pdf) | A shared-memory synchronization classification and read/write implementation criterion based on consistent commutativity/overwriting. It does not establish Byzantine quorum authentication, durable journals, cross-epoch refunds, or the consensus number of CBCL's whole combined interface. It supports semantic classification rather than deployment claims. |

## Additional approaches and newer evidence

[AT2](https://arxiv.org/abs/1812.10844) supplies the foundational asset-transfer
baseline omitted from the named section. Its deterministic and probabilistic
message-passing variants must not be conflated: replacing deterministic quorum
evidence with sampling changes the guarantee. The shared-memory consensus-number
result also does not erase ownership assumptions.

[Pastro, sections 2–6](https://drops.dagstuhl.de/opus/volltexte/2021/14830/pdf/LIPIcs-DISC-2021-28.pdf)
is a substantive omitted consensus-free family: asynchronous asset transfer with
dynamic proof-of-stake configurations and lattice-agreement machinery. Its
less-than-one-third adversarial stake assumption and forever-correct-process
progress conditions differ from a fixed CBCL committee. It is relevant if dynamic
membership becomes a requirement, not a reason to insert reconfiguration now.

[Zef](https://sonnino.com/papers/zef.pdf) extends FastPay with private off-chain
coin certificates, blind threshold credentials and deactivatable accounts.
Unique non-replayable identifiers and deletion rules offer a concrete storage
research direction. They cannot justify deleting arbitrary CBCL epoch history,
whose delayed certificates and permanent cancellation evidence have different
obligations. A claimed bound must include identifiers, tombstones, client history
and any key-rotation assumptions, not merely active account payloads.

[PaxPay, sections 3–5 and 8](https://drops.dagstuhl.de/storage/00lipics/lipics-vol354-aft2025/html/LIPIcs.AFT.2025.3/LIPIcs.AFT.2025.3.html)
is an important 2025 omission. It provides fully private consensus-free transfers
using NIZKs, blind signatures and consumable coins, assuming anonymous secure
reliable channels, a static network-ignorant adversary, and fewer than one third
Byzantine validators. Correct users issue operations sequentially. Conflicting
spends can lock their coins; the discussion says consensus is required to unlock
that case. Thus privacy is possible in a consensus-free design, but this is not a
drop-in recovery solution for CBCL concurrent owners. The privacy/network/setup
assumptions need their own specification if ever adopted.

[The 2026 Blocklace memory-exhaustion analysis](https://arxiv.org/html/2607.15185v1)
shows why finite eventual Byzantine harm is insufficient as a resource bound:
new identities can force acceptance of arbitrarily large useless evidence, up to
the identifier space. The proposed mitigation restricts admitted identities.
This does not refute SPEC-025's fixed-roster safety proof. It strengthens the host
requirement to bound admitted identities, operation payloads and retained evidence
before claiming production DoS resistance.

[The Consensus Number of Untraceable Cryptocurrencies, 2026 full version](https://arxiv.org/html/2607.20929v1)
studies specific linear-state and constant-state untraceable asset-transfer
objects. Its linear-state object has consensus number two; constant-state
masking-set replacement incurs stronger synchronization and fairness costs.
These are object-specific results, not a blanket impossibility of private
consensus-free payments. In particular, do not use them to dismiss PaxPay without
matching object, ownership, return-value and adversary definitions.

## Review conclusion and provenance

The current specification correctly separates certificate consistency from
agreement termination and explicitly names the storage and crypto boundaries.
Its conservative concurrency is a different tradeoff from FIFO owner protocols;
the literature does not establish that it is universally superior or optimal.
The next useful research obligation is an explicit progress profile for a
disciplined owner, relay availability, cancellations and residual capacity, plus
a decision about local versus complete account reads. The maintainer owns those
follow-ups; none may weaken the no-consensus constraint through recovery.

This review screened every named entry in the requested section and followed
primary-source trails to the additional works above. It is a targeted gap review,
not a guarantee of exhaustive state-of-the-art coverage. Performance claims were
not reproduced, private-payment cryptography was not audited, and publications'
proofs were not mechanically reverified here.

Primary URLs, versions and retrieval hashes remain in
`outputs/consensusless-literature-evidence/crawl-manifest.json`. Raw crawl records
and copied paper text are archived at commit `713b599`, rather than vendored in
the current tree. The initial GitHub
HTML crawl returned an error page despite successful process exit; the raw GitHub
README retry contains the requested section. Full papers were read through web
HTML/PDF extraction as indicated above; PaxPay's PDF was additionally inspected
with local pdftotext. The coordinator should record this review and actionable
findings in the existing Elephant theory. No independent Elephant signer was
claimed: this subprocess sees the shared default local identity.
