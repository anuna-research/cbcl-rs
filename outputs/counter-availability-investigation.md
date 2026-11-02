# Consensus-free counter availability: literature and Lean audit

## Orientation

The current protocol does not yet meet the requested availability contract. The issue is not just slow scheduling: conservative signing capacity can reject a fully funded unit debit, and racing execution with cancellation can split the honest votes so that neither outcome completes. Both mechanisms now have kernel-checked counterexamples against the current model.

The literature supports a narrower positive direction: honest single-owner protocols can finish without consensus when the client controls issuance, dependencies become available and honest validators eventually respond. Stingray's owned-counter lifecycle additionally invokes conversion to a standard owned object for the residual balance. Its version-DAG merging and shared-object FastUnlock are different mechanisms; FastUnlock uses consensus and is outside the user's accepted design.

The recommended next design is one language-selected protocol with a disciplined owner driver and an internally specified, safely fenced exclusive completion path for payments that do not fit the concurrent budget. The completion path is a proposal, not implemented, proved safe or guaranteed live here. Unrestricted collective pools require a separate decision about contention and ownership; splitting rights changes their semantics and must not happen silently.

This work performs the previously agreed Lean-first next step: produce either a stronger lifecycle proof or a counterexample identifying a necessary change. It produces counterexamples, rather than asserting the stronger proof. Runtime remains unchanged at commit `3bacf55`. Next actor: CBCL maintainer, to choose and specify the owner completion contract before modifying Rust. The user requires no consensus and rejects indefinite lockup; neither condition is waived.

## Availability contract to target

For a correct logical owner, a finite, legitimately funded request must eventually produce a verified effects certificate, assuming at most f Byzantine validators among 3f+1, reliable eventual delivery between correct parties, persistent journals, fair service and available required evidence. A request being affordable in the account must not be rejected forever merely because it exceeds the concurrent signing fraction. Every positive base-unit remainder must have a completion path. Repeated submission by an honest driver must preserve one operation identity; unrelated accounts must not be held hostage by a faulty owner.

“Available required evidence” means eventual delivery or retrievability of already-generated authenticated prerequisites. It does not assume the target effects certificate, a handoff certificate or a cancellation certificate exists. When the driver accepts a waiting request as funded, it durably reserves the actual rights required in each resource coordinate so later requests cannot consume that funding.

This is eventual completion, not bounded latency in an asynchronous network. A request exceeding actual authorized funds may return a durable non-spend outcome; temporary inability to obtain a quorum is not proof of failure. A guarantee for correct owners is not a guarantee that a Byzantine owner can always recover its own deliberately conflicting history.

A correct logical owner requires a coherent submission policy. Two devices independently signing conflicting requests with one key do not become one well-behaved writer merely by sharing an identity. We must either model durable owner-local coordination, allocate disjoint device rights, or adopt a different shared-account contract. A distributed lock among devices cannot be hidden under the phrase “client coordination.”

## Finding: residual balance rejection

The existing signing guard is:

```text
(2f+1) × validator's charged costs ≤ (f+1) × version allocation
```

For four validators and one Byzantine fault, an otherwise idle one-unit account attempting a one-unit debit requires `3 ≤ 2`. No honest validator may sign. There is no prior reservation to cancel or refund.

`counter-liveness-evidence/ResidualBalanceAudit.lean` instantiates the CURRENT multi-parent model with one authorized unit debit, initial capacity one, no external credits and no cancellation. It proves:

- Honest signing is disabled in every state, independently of graph shape.
- No accepted execution obtains an honest operation signature, an operation certificate or a final certificate.
- A concrete valid successor is recorded and adopted by every honest validator; signing is still disabled.
- An actual infinite replay execution satisfies target signing/effect weak fairness while never finalizing.

The graph theorem quantifies over any finite static version DAG with the fixed unit-allocation manifest family and fixed operation target version. Arbitrary nodes need not all have valid parent structures; the concrete successor witness is statically valid. The example starts with one unit: it is not a verified spend-down trace from a larger starting balance. It establishes that version advancement alone does not guarantee full-balance access under these guards. It is not an impossibility theorem about all consensus-free protocols or future mode-conversion mechanisms.

The matching Rust guard is `Replica::budget` in `crates/cbcl-core/src/quorum/engine.rs`. The arithmetic corresponds directly, but this audit is not a universal Rust refinement proof or a live Rust reproduction. The existing liveness theorem's `FitsEnvelope` deliberately excludes this instance, so the finding does not invalidate that theorem. It shows why the theorem is insufficient for the newly required business availability.

## Finding: execution/cancellation split

`counter-liveness-evidence/CancellationRaceAudit.lean` constructs an accepted execution with initial capacity three and one debit of two. All three honest validators sign, so an operation certificate exists. The configuration permits both operation and cancellation:

```text
                   honest 0    honest 1    honest 2    Byzantine 3
operation vote        yes         yes         yes        silent
outcome vote         effect       fence       fence      silent

Effects: 1 < quorum 3. Cancellation: 2 < quorum 3.
```

The infinite accepted suffix has neither finality nor cancellation; local charges remain reserved. Useful target signing, effects and new-fence actions satisfy weak fairness: each honest validator has already acted or is permanently disabled on the other side. Repeated idempotent commands do not create the missing votes.

This is an ideal authorized race: the generic configuration has authorization booleans, not an explicit actor/request issuance history. It does not establish a concrete network exploit or prove that a correctly designed owner driver must produce the race. The witness has no successor versions (`V=0`) and does not rule out a correctly designed recovery extension. The current liveness theorem assumes no cancellation authorization, so this is a refutation of a stronger finalize-or-cancel claim, not a contradiction in the existing proof.

The matching Rust `Event::Effect`, `Event::Fence` and `Event::Release` guards enforce the same permanent effects/fence exclusion and cancellation-quorum release. Merely publishing those APIs does not establish eventual resolution. Recommending “cancel on timeout” would expose exactly the wrong missing proof obligation.

## Literature findings

The source IDs below index `counter-liveness-evidence/sources.json` and its ar-crawl session. These are scoped primary-source readings, not an exhaustive literature survey.

| Source | Relevant progress mechanism | Assumptions and limits | Implication for CBCL |
|---|---|---|---|
| L01: Stingray v1, §4.3, Algorithm 2, Appendix A.1 | Owner limits submissions to the signing envelope, carries submitted transactions into version updates, and uses owned-object conversion for the small residual | Algorithm 2 may return Error if a request still exceeds budget after an update. The theorem covers its submitted operations, not every arbitrary globally affordable application request. The conversion narrative/client branch is not a detailed conversion refinement for CBCL | Add the missing client lifecycle and an explicitly proved full-balance completion mechanism; a budget scheduler alone is insufficient |
| L01: Stingray, §5.3/§6 and Appendix D | Multi-parent versions for collective counters; consensus-backed FastUnlock for contention | Optimistic DAG merging does not imply general progress. Repeated unlocking can require additional contention treatment | Do not promise collective recovery from merging alone; FastUnlock cannot be silently imported under no-consensus requirements |
| L02: FastPay v3, §4.5 and §5 | One correct sender issues consecutive sequence numbers, signs one order per sequence and propagates certificates | Sufficient funds and a correct client/proxy lifecycle are needed. Excessive signed requests can block; certified payments are not cancelable. Faulty senders can lock their own accounts | Per-owner serialization can be consensus-free, but it is an ownership restriction and a new protocol argument, not “just a queue” |
| L03: AT2 v3, §§2–4 | Per-owner transfer sequencing, dependencies and secure broadcast | Correct owners and correct-operation validity; faulty owners need not terminate. Read/failed-transfer semantics differ from successful-transfer guarantees | A no-global-order payment lane is a credible direction; full broadcast/validation properties must be implemented, not replaced by signature counting |
| L04: Astro, §§II–IV | Per-client xlog sequence, broadcast and credit propagation | Basic client termination assumes a correct client AND correct representative replica. Astro II needs extra credit evidence to address lack of totality | The host must implement reliable submission/relay and portable credit recovery. A hidden single untrusted proxy must not be assumed live |
| L05: CryptoConcurrency v2, §3.2/§5 and recovery sections | Compatible shared-account transactions progress, with account-local consensus in recovery | A “correct account” has all correct owners; correct/Byzantine co-ownership is excluded from its guarantee. Consensus avoidance is eventual after overspending attempts cease. Termination can return failure | It does not supply the requested unconditional consensus-free shared-pool recovery |
| Consensus-number paper, §§3–6 | Single-owner asset-transfer object has consensus number one; k-shared object has consensus number k | Shared-memory wait-free/crash model and the specified object semantics; not a theorem covering every relaxed Byzantine service | Be precise about shared-account semantics rather than citing the result as a blanket prohibition on every collaborative counter |

Primary links:

- [Stingray v1](https://arxiv.org/html/2501.06531v1), especially Algorithm 2 and Appendix A.1.
- [FastPay v3](https://arxiv.org/html/2003.11506v3), especially client behavior and liveness proof.
- [AT2 v3](https://arxiv.org/html/1812.10844v3).
- [Astro](https://arxiv.org/html/2004.13184v1).
- [CryptoConcurrency v2](https://arxiv.org/html/2212.04895v2).
- [The Consensus Number of a Cryptocurrency](https://pmc.ncbi.nlm.nih.gov/articles/PMC8882574/). The ar-crawl browser attempt was blocked; its text was inspected with the web reader during this investigation and the preceding bibliography work. The blocked capture is not counted as usable paper evidence.

A targeted additional search also surfaced [Fast, Private and Regulated Payments in Asynchronous Networks](https://eprint.iacr.org/2025/098.pdf) and [BRAPTOR](https://doi.org/10.1016/j.compeleceng.2024.109636). These were abstract-screened leads only. Neither supplies a verified cure for our reservation/version lifecycle in this audit; BRAPTOR explicitly includes a total-order consensus component for general applications. No latest-state-of-the-art completeness claim is made.

## Candidate design to formalize next

### A disciplined owner driver

The owner keeps a durable submitted-operation journal and reserves BOTH rights and optional headroom before issuing requests. Concurrently issued costs fit the conservative envelope jointly; certificate delivery, rather than a UI timeout, determines settlement. Pending effects certificates are retransmitted and relayed. The driver does not issue competing cancellation requests while completion is the chosen outcome.

This makes a useful honest-owner hypothesis executable. It does not solve dust, large-request availability, externally coordinated devices or general collective contention. Merely asking applications to stay within the envelope would weaken the requirement instead of solving it.

### An exclusive continuation for requests outside the concurrent envelope

When an outside-envelope request is selected, the proposed driver first stops issuing new old-mode resource-consuming operations and snapshots a finite durable submitted set. Fair owner-local request selection prevents later small requests from indefinitely bypassing the waiting request. It drains that fixed set, then obtains the necessary validator-side closure evidence, proves which old obligations remain possible, and moves the remaining resource vector into a per-owner continuation. Freezing client issuance before draining is distinct from sealing validators before pending old signatures can finish. That continuation can certify a funded full-balance debit without applying the fractional concurrent budget again. New requests within one continuation are ordered by that owner; accounts remain independent. This is a proposal for one language-selected protocol, not a host protocol switch or backward compatibility path.

The critical safety question is the transition: no old concurrent certificate can remain spendable in addition to the same capacity in the continuation. We cannot simply change the budget multiplier, clear the journals or declare the remaining balance known. Possible withheld old certificates, zero-cost signatures, incoming final credits, cancellation refunds and BOTH resource coordinates must all be preserved or excluded by actual certificates.

A correct single owner can propose a unique, complete continuation statement. Quorum endorsement can confirm that statement without becoming an oracle that chooses between arbitrary competing owners. If the proof assumes a winner is eventually selected among conflicting proposals, it has reintroduced the very problem we are trying to avoid. The first model should permit an honest owner with eventual delivery and all Byzantine validators silent; no timing bound or Byzantine response may close the proof.

This continuation could be invoked for a large payment as well as the last unit. Splitting an application payment into smaller separately finalized transfers changes its atomicity and is not an equivalent fix unless the user explicitly chooses that semantic change.

### Collective scopes

The existing shared pool allows independent actors to compete for the same remaining units. A disciplined SINGLE-owner argument does not cover that case. Partitioning actor rights avoids some conflicts but changes access to the pool; it cannot be introduced as an invisible optimization. Generic contention resolution by consensus-backed FastUnlock or CryptoConcurrency recovery violates the current no-consensus requirement.

The maintainer must choose the shared-pool availability contract separately: exclusive assigned rights, an explicit owner/scheduler trust boundary, or another precisely defined relaxed resource object with its own safety/progress proof. This report does not assert a deterministic fully asynchronous arbitrary-contention solution.

## Lean-first proof and acceptance obligations

The next candidate model must derive, rather than assume:

1. Honest-owner batches always fit each honest validator's guards, including both resource dimensions and delayed deliveries.
2. All submitted in-envelope operations eventually obtain observed effects certificates without Byzantine cooperation.
3. A funded outside-envelope request is eventually selected, owner issuance freezes before a finite submitted-set drain, and a correct owner can complete the closure/continuation handoff without starvation from new requests, assumed agreement termination or a globally authoritative balance.
4. Late old certificates cannot double-count capacity after continuation activation; historical journals remain permanent.
5. An affordable single-unit or full-balance request eventually completes. Include an explicit initial-unit case and a separate real spend-down trace, not just asymptotic arithmetic or no-counterexample testing.
6. The owner never enters the execution/cancellation split in valid driver runs. If supported cancellation races are allowed, prove a separate eventual-outcome contract rather than assuming refund quorums appear.
7. Other accounts remain live when a different owner equivocates or stops. For collective scopes, name the additional ownership/availability assumption.
8. Only after these model results and independent review: add Rust correspondence traces, adversarial schedules and real-network evidence-delivery tests. Current throughput benchmarks are not evidence of these availability guarantees.

These are proposed acceptance obligations for specification work, not completed requirements or existing implementation properties.

## Evidence and status

The ar-crawl session is `a53a8d66-005b-40fc-99b2-f2de308f7e93`; commands, recording and full captures are retained locally. The manifest records source versions, usable/blocked captures and hashes. The search is purposive; queries and abstract-screened leads are recorded separately. Raw copyrighted paper captures are not intended for repository vendoring.

Both new audits import the committed current model and were checked with Lean's kernel. Their printed dependencies are standard `propext`, `Quot.sound` and, for the residual certificate lemmas, `Classical.choice`; no admitted proof is present. The model-specific counterexamples do not implement a replacement runtime. The generic model uses ideal authorization and certificate-delivery abstractions; cryptography, physical durability, packet routing and universal Rust equivalence remain separate.

Independent adversarial review: [[counter-availability-review]]. Signed findings and next-step evidence are recorded in local Elephant theory `cbcl-counter-availability`. See `outputs/counter-liveness-evidence/README.md` for commands, scope and the distinction between signed research assertions and machine-checked Lean results.
