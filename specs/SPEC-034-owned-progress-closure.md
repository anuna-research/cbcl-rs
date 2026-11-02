---
id: SPEC-034
title: Closing correct-owner protocol progress obligations
version: 0.1.0
status: in progress
last-updated: 2026-11-02
---

# Correct-owner protocol progress

## Orientation

The user wants to establish protocol-level deadlock freedom for the account-owned
lifecycle in [[SPEC-033-owned-counter-lifecycle]]. The current proof assumes owner
readiness conditions; it does not derive them from every executable owner schedule.
This work closes those obligations without consensus, timeout refunds or a winner
oracle. A correct coherent owner, available honest quorum, eventual delivery and
service/commits, retained evidence and finite configured capacity remain explicit
assumptions.

Named failures: **stale-sign fairness** requires old signatures after observed
completion and sealing; **unobserved completion** stops retries because votes
exist globally although the owner never received them; **lost adoption retry**
leaves a validator behind when metadata/adoption arrives out of order. None may
be hidden in an assumed final certificate or an opaque SignAllowed premise.

```text
accepted FIFO input + actual resource reservation
                    |
          executable owner decisions
                    |
   persistent dependency/certificate relay
                    |
 validator catches up along verified owned ancestry
                    |
 honest vote -> retained delivery -> owner verifies QC
                    |
            owner journals Complete
```

The proof target is per-request completion, including the final unit, not a timing
bound. Necessary honest retry work persists while the owner lacks its certificate.
After observed completion, stale jobs need not execute. Later arrivals cannot
bypass a selected request or seal. Collective contention and conflicting owners
are excluded. Product-model proofs and finite Rust correspondence must be
separated from universal Rust/network/cryptographic equivalence.

Controls: [[SPEC-034-owned-progress-closure#REQ-3400]] observed progress;
[[SPEC-034-owned-progress-closure#REQ-3401]] catch-up;
[[SPEC-034-owned-progress-closure#REQ-3402]] dependency relay;
[[SPEC-034-owned-progress-closure#REQ-3403]] derived readiness;
[[SPEC-034-owned-progress-closure#REQ-3404]] adversarial acceptance.

## Amendment Channels

The user authorizes local proof, protocol implementation and regression repairs.
Consensus-free semantics, permanent history and authenticated capacity cannot be
waived. Tier 1 review includes independent adversarial and fresh Orientation
comprehension checks. Human domain review precedes production deployment; it does
not block authorized local proof/implementation.

## Requirements

### REQ-3400

Progress MUST use actual owner-observed verified certificates. Unreceived Byzantine
votes MUST NOT disable necessary honest work. Fairness MUST NOT demand stale
signatures after observed completion. A terminal-certificate premise or existence
of an enabled transition MUST NOT substitute for eventual-completion proof.
Trace: [[SPEC-034-owned-progress-closure#TEST-3400]].

### REQ-3401

A lagging honest validator MUST catch up to a requested Owned version using retained
verified ancestry/root QC without replay of lost adoption requests. Catch-up MUST
preserve scope, direct-parent order, full historical signatures, phase, rank and
permanent slots. Invalid/missing paths and failed atomic writes MUST expose no
vote or discard evidence. Concurrent/collective semantics MUST remain scoped.
Trace: [[SPEC-034-owned-progress-closure#TEST-3401]].

### REQ-3402

Correct-owner publication MUST retain/relay prerequisites until observed completion.
Receivers MUST retry dependency processing to a finite fixed point or report explicit
missing inputs. One-shot reliable packet arrival MUST NOT be called sufficient.
Relay input MUST exclude another validator's local Sign/Adopt/Fence decisions.
Every object MUST traverse normal authentication/grammar/book guards.
Trace: [[SPEC-034-owned-progress-closure#TEST-3402]].

### REQ-3403

An executable owner/protocol product MUST derive funded reservations, issued-envelope
bounds, finite drain, complete unique seal intent, FIFO/history coverage and
full-capacity readiness from owner transitions and validated admitted input.
Progress MUST end in journaled completion of the same immutable issued identity
with observed EffectsQC. Delivery, fair honest processing, eventual successful
nonforking commits and sufficient capacity MAY be assumptions. Desired final QC or
owner readiness MUST NOT simply be assumed. Open obligations MUST remain explicit.
Trace: [[SPEC-034-owned-progress-closure#TEST-3403]].

### REQ-3404

Evidence MUST cover Byzantine-assisted early QCs, unsigned lagging honest validators,
reordered dependencies, retry/restart, later Byzantine silence, full-balance spending
and concurrent arrivals. Guard mutations MUST be detected. Independent review MUST
assess actual enabling premises and model/implementation correspondence limits.
Trace: [[SPEC-034-owned-progress-closure#TEST-3404]].

## Contracts

### CON-3400

Reuse typed Act/DagVersion/OwnedSealRequest/Certificate recognition. Relay grammar is
a closed tagged union of those public evidence types, excluding local decisions.
Catch-up is bounded by the configured version catalogue and durably applied before
vote exposure. Evidence batches may contain individually atomic journal events;
partial progress MUST be retained/reported, never described as atomic rollback.
Trace: [[SPEC-034-owned-progress-closure#REQ-3401]], [[SPEC-034-owned-progress-closure#REQ-3402]].

### CON-3401

Separate durable votes from received signatures and verified certificates. Byzantine
publication may be early, withheld, conflicting or absent. Delivery guarantees apply
to honest retained work. The owner issues only journaled immutable requests,
publishes one seal intent after observed drain, and completes an owned slot before
advancing. Source-equivalence claims require their own verification evidence.
Trace: [[SPEC-034-owned-progress-closure#REQ-3400]], [[SPEC-034-owned-progress-closure#REQ-3403]].

## Tests

### TEST-3400

Core: kernel-check observed-quorum progress with withheld Byzantine votes and early
certificates. Completed requests need no stale signatures. Removing receipt from
the completion condition must fail a negative control.
Validates: [[SPEC-034-owned-progress-closure#REQ-3400]].

### TEST-3401

Core: reject newest adoption before ancestors arrive, deliver metadata later, then
finish the current payment without resending old adoption jobs. Check history,
incompatible branches, failed writes and restart. Removing catch-up must fail.
Validates: [[SPEC-034-owned-progress-closure#REQ-3401]].

### TEST-3402

Core: reversed evidence batches converge; partial batches report missing inputs and
finish after later evidence. Forged evidence and local-decision injection reject.
Every accepted certificate must be genuine; no synthetic QC is admitted.
Validates: [[SPEC-034-owned-progress-closure#REQ-3402]].

### TEST-3403

Depth: initialized product executions derive observed Complete for every admitted
funded request under named environmental conditions, without opaque readiness or
terminal-QC assumptions. Audit standard axioms. Until this capstone exists,
implementation-wide deadlock freedom remains unproved.
Validates: [[SPEC-034-owned-progress-closure#REQ-3403]].

### TEST-3404

Core: independent adversarial review, relevant Rust/Lean tests, no_std, formatting
and mutations. Shared traces compare actual guards rather than a second simulator.
Validates: [[SPEC-034-owned-progress-closure#REQ-3404]].

## Open obligations

Owner: coordinator. The universal product completion theorem and Rust refinement
remain active work. Close observed-progress and dependency/catch-up seams before
composing the capstone; passing partial checks does not discharge the capstone.

## Implementation checkpoint

Retained publication, bounded fixed-point evidence import, history-compatible
catch-up and owner certificate feedback are implemented. Lean components prove
retry closure, observed-quorum retirement and admission-derived full-allocation
head funding. Independent review and the fresh-context Orientation gate are
recorded in [[owned-progress-evidence]]. These satisfy component milestones;
TEST-3403 and the universal executable-owner completion obligation remain open.
