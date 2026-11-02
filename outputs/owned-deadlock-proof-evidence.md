# Account-owned product completion proof

Date: 2026-11-02. Governing specification: [[SPEC-034-owned-progress-closure]].
The verified runtime/component milestone was committed as `3a4fa5d` before this work.

## Result and exact boundary

The initialized finite-capacity Lean product proves:

```text
for every fair product execution, request i and admission time t:
    accepted(i, t)
        => exists u >= t: owner journal contains Complete(i, u)
        => Complete(i) remains true thereafter
```

The theorem names are `admitted_eventually_complete` and
`admitted_eventually_always_complete` in `OwnerTermination.lean`. The initialized
owner transitions, validator actions, retained metadata/proof imports, signature
receipts, certificate formation and completion record belong to one execution.
No desired QC, SignAllowed, finite drain, unique handoff or funded-head readiness
is passed as a liveness premise.

This is a full completion theorem for the stated abstract protocol product. It is
not a universal Rust source-equivalence theorem. Nat/Int resources and finite
symbolic identities abstract checked machine arithmetic and serialized wire IDs.
Native operation/event/version/evidence/transport/rank/byte capacities must be
large enough for the accepted catalogue and its complete retained proof closure.
That source-level extraction and capacity verification remain open.

## Why the proof closes the earlier gap

```text
initialized owner + funded admissions
       |
       +-- issued concurrent batch stays inside its envelope
       +-- freeze stops new concurrent issuance
       +-- observed drain covers all possible old honest signatures
       +-- one immutable root intent + actual received quorum
       +-- owned version snapshots preserve the admitted head's funding
       +-- successor history contains every earlier issued identity
       |
 retained dependency import -> local adoption -> vote or genuine QC feedback
       |
 actual received signatures -> owner verifies EffectsQC -> durable Complete
```

All first-time structural facts are monotone and come from finite catalogues.
After the last such change a hypothetical stalled state would be stationary.
The saturated-state lemma derives a concrete necessary owner/honest action for
an incomplete request, contradicting task-level fair service. Stabilization does
not rely on a full journal refusing writes.

Necessary-work predicates retire operation/effects/seal signatures after the
owner observes the corresponding QC. Private Byzantine votes cannot retire work.
Old data delivery remains necessary when a published later version references it;
external proof imports require a pinned snapshot reference. There is no fairness
requirement once no accepted request is pending. Byzantine actors may stay silent
or sign outside honest budget/effects guards, but cannot forge owner identities or
honest signatures. Actual quorum counting uses the pinned distinct committee.

## Assumptions

One correct nonforking durable owner and correctly serviced owner replica; a
committee with an honest core of 2f+1 and at most f other members; ideal signature
and immutable identity recognition; retained authentic incoming proofs with finite
acyclic dependencies; fair service/delivery/successful journal turns for each
retained necessary honest job; sufficient configured capacity. Admissions can
arrive arbitrarily late within the finite catalogue. No timing bound follows.
Permanent outages, lost keys/storage, conflicting owners and arbitrary collective
contention are outside this theorem. No consensus fallback or timeout refund is
introduced.

## Review and validation checkpoint

The independent cross-model reviewer `product_adversary` compiled both theorem
files and audited their axioms. Review found and drove corrections to local QC
prerequisites, observed-root signing guards, stale-work fairness, incoming evidence,
owner adoption and early seal-certificate feedback. Its final remaining correction,
requiring recipient root metadata before a delivered root QC is locally verified,
was applied. The corrected product, completion theorem and executable fair-run witness all
compile. The reviewer found no remaining blocker to the product-only claim,
keeping the native Rust refinement boundaries above explicit.


## Reproduction and acceptance

From the repository root:

```sh
python3 tools/verify-owned-deadlock.py --mutations
```

From `lean-cbcl/`:

```sh
lake build
lake env lean OwnerProductAudit.lean
```

The full library build passed (119 jobs). The axiom audit covers reachability,
funding, envelope/native fractional-budget compatibility, saturation, absence of
a pending deadlock, eventual completion, persistent completion and the fair witness.
Only `propext`, `Classical.choice` and `Quot.sound` occur; there is no `sorryAx`.

Negative controls reject removing drain before a manifest, pinning unfunded books,
requiring stale operation signatures after owner observation, and accepting a root
QC before local root-proposal metadata. The root guard's mutation also adapts its
proof term, so its failure comes from the executable behavior witness. Mutation
compilations use temporary fused sources and never change the worktree.

The executable fair infinite witness contains early root, operation and effects
certificates supported by validators 0, 1 and Byzantine 3; honest 2 misses the first
exchange. After the first completion validator 3 takes no further action. Validator
2 imports old proof/ancestry and the three honest validators finish the last-unit
request. A finite script followed by replay is proved to satisfy necessary-job
fairness, establishing a non-vacuous execution of the theorem's assumptions.

Additional traces kernel-check later admission, reordered external-proof imports,
rejection before dependency readiness, and a later incoming certificate leaving
an already pinned version's allocation and snapshot unchanged. An income-backed
spend-down also finishes with allocation one at the last request.

The fresh-context `capstone_orientation` reader correctly predicted early-QC
catch-up, no retirement on private unreceived QCs, the REQ-3403 readiness control,
and the distinction from universal Rust verification and timing guarantees. No
comprehension defect was found. Independent review was performed by
`product_adversary` (gpt-6-astra); it compiled and audited the actual proof files.

The universal Rust proof remains open: symbolic request indices denote immutable
issued identities within this model; their actual canonical bytes, hashes and
signature domains need source-level extraction. Native limit and checked-number
extraction and deployed host compliance are likewise distinct work. This is not a
claim of unconditional fund recovery under permanent failure.

The existing lifecycle verifier also passed after regenerating Cargo artifacts
following local disk exhaustion during compilation. It checks the shared prior
Lean oracle, owned Rust adversarial tests, and real Ed25519/durable lifecycle. No
Rust runtime source changed in this proof increment. The SPEC-034 plan now records
the product capstone as verified/completed and keeps universal Rust refinement
and native capacity/wire extraction explicitly outstanding. Source hashes and
verification scope are retained in `outputs/owned-progress/capstone-verification.json`.
