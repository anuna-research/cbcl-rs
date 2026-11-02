---
title: Owned counter lifecycle evidence
id: owned-lifecycle-evidence
mode: reference
---

# Owned counter lifecycle evidence

[[SPEC-033-owned-counter-lifecycle]] replaces the account-owned residual-budget
stall with a permanent, authenticated handoff and full-capacity continuation.
Collective contention remains under [[SPEC-031-unified-quorum-dag]].

## Model and proof boundary

`OwnedLifecycle.lean` models one resource scope, finite immutable catalogues,
an honest core of 2f+1 among 3f+1, ideal authentication, permanent journals and
monotone vote-derived certificates. It proves historical coverage of late old
certificates, unique certified roots, comparable certified histories, one certified
choice per version rank, prior-cancellation exclusion, and numeric nonnegativity
for every resource coordinate. External incoming credits have a separate disjoint
catalogue and authenticated receipt transition; duplicate receipt stutters. Their
identity/context/recipient verification is the ideal certificate-verifier boundary,
not a new globally ordered ledger. External entries exclude credits already
included in genesis/root books or the internal transaction catalogue.

`finite_batch_drains` applies the existing concurrent-envelope liveness theorem to
the old projection of the same initialized execution. It requires a frozen finite
authorized batch, stable source versions, no owner cancellation and fair honest
service. `correct_owner_closure` derives compatible partial seals from the owner's
single signed intent. `seal_after_drain` derives a handoff quorum from drained
books and complete historical coverage. `eventually_final` derives both owned
voting quorums from explicit funded-prefix/history and prerequisite-availability
conditions; fairness quantifies only useful honest actions, never Byzantine ones.
`client_observes_finality` separately derives an observed certificate under reliable
vote delivery and retention. There is no wall-clock latency bound.

This is an abstract protocol proof, **not a universal refinement of the Rust owner
driver, wire decoder, network, operating system, cryptography or filesystem**.
The concrete owner driver enforces FIFO, frozen issuance, durable publication and
one operation per owned version. Its correspondence is checked by selected actual
execution traces and recovery/adversarial tests, not by extraction or a universal
source-equivalence theorem. In particular, the Lean ranked-history abstraction
omits concrete parent-map traversal and models owner issuance/readiness conditions
explicitly; it does not prove the Rust driver generates those conditions on every
possible host schedule. Pre-seal account/collective DAG behavior retains its
existing model/claim boundaries. Catalogue and configured storage/service capacity
must remain available; no unbounded resource-exhaustion resistance is claimed.

## Executable evidence

`OwnedLifecycle.lean` includes kernel-checked initial-unit, real 4+1 spend-down,
silent-fourth-validator, burn/mint/headroom cycle, late authenticated incoming-credit
and pre-fence rejection witnesses. `OwnedLifecycleAudit.lean` prints axiom dependencies.
`OwnedLifecycleOracle.lean` exports actual `perform` guards and state snapshots.
`owned-lifecycle-lean.json` is that generated output. Rust's
`owned_shared_lean_transition_traces` compares all state snapshots after each action:
per-validator seals/signatures/effects, operation/effects QCs and balances. Metadata
receipt, verified QC relay and adoption are concrete stuttering steps between
shared actions; the two traces cover initial-unit and spend-down schedules.

Targeted Rust tests additionally cover FIFO freeze/drain/restart, failed owner and
validator appends, exact retries, unfunded admission, full allocation, version-slot
conflicts, distinct owner signature domains, phase binding/downgrade rejection,
future-root pre-fences, account isolation and late cross-account credits.
A separate host harness test uses real Ed25519, fsync-backed validator and owner
journals, one silent validator, client observation and restart.

Independent review identified and drove repairs for fairness scope, postcompletion
readiness, missing external incoming accounting, observer delivery, cross-phase
pre-fences and provisional future-root signatures. The final repair binds
Concurrent/Owned phase into manifest identity, prevents Owned adoption/signing
before seal QC, forbids phase downgrade, and retains cancellation exclusions.
Four deliberate Rust guard mutations (slot, local seal closure, owner signature
domain and prior-fence exclusion) were detected by targeted behavioral regressions.
A weakened Lean history guard was rejected by the kernel-checked invariant proofs.
`python3 tools/verify-owned-lifecycle.py --mutations` reproduces these checks and
restores the implementation in a finally block.
Final validation results and remaining review findings are recorded below.


## Final validation

2026-11-01, `state-rules-spec`, worktree `/private/tmp/cbcl-bounded-counter`:

- `CARGO_INCREMENTAL=0 cargo test -p cbcl-core -p cbcl-parser -p cbcl-quorum-e2e --tests --offline`: 1,414 passed, no failures, 11 existing ignored tests; no compiler warnings.
- `lake build`: complete library build passed, including OwnedLifecycle and its kernel-checked witnesses.
- `lake env lean OwnedLifecycleAudit.lean`: standard `propext`, `Quot.sound`, `Classical.choice` only; no admitted axioms.
- `python3 tools/verify-owned-lifecycle.py --mutations`: oracle equality, runtime traces, real-signature/durable journals, all four behavioral guard mutations and weakened-history proof rejection passed; source restored afterward.
- `CARGO_INCREMENTAL=0 cargo check -p cbcl-core --no-default-features --offline`: passed.
- Changed Rust file formatting and `git diff --check`: passed.

The durable owner-journal harness additionally rejects process-lock conflicts,
wrong context, wrong append sequence and torn suffixes. Serialized seal/journal
structures reject unknown authority/cache fields. Recovery rejects forged owner
completion and changed issuance rather than trusting a cached balance.

The whole-vault zetl check still reports existing cross-vault/dead-link issues;
no whole-repository documentation-health pass is claimed. Backlinks for the
amended [[SPEC-031-unified-quorum-dag]] were inspected with an uncached specs-vault
query before amendment. Source captures and tool logs remain local and ignored;
the proof, oracle fixture, reproduction tool, curated findings and source manifests
are retained.

## Independent gates

The fresh-context Orientation reader (`owned_orientation_gate`) correctly predicted
initial-unit conversion, frozen FIFO retries, owned full-capacity completion,
collective exclusion and the coherent-owner progress boundary. No orientation
ambiguity remained. The independent cross-model adversarial reviewer
(`counter_liveness_review`, gpt-6-astra) inspected the actual Lean and Rust changes,
independently compiled the model and reran the then-current owned test suite.

The review drove the fairness, incoming-credit, client-observation and cancellation
repairs described above. The final assessment found no additional concrete blocker
in correct coherent-owner FIFO/reservation/freeze/drain/issuance/recovery behavior.
Approval is scoped to the abstract proof and concrete tested behavior, with the
universal driver/source/network/identity-extraction refinement obligations stated
in the proof boundary. The review's remaining minor API discrepancy—rejecting a
Concurrent manifest in `Context::owned_seal_request`—was corrected and covered by
the phase-binding regression. This is local implementation validation, not a
production deployment or universal formal-verification certificate.


## Protocol-stall terminology

The replacement targets protocol-induced residual-budget freezes and split
execution/cancellation outcomes in correct-owner operation. Its completion path
is freeze, finite drain without additional spending allowance, permanent seal QC,
then full-allocation continuation. The driver never cancels issued work. The
intended account contract is eventual observed finality for a funded FIFO request
under the stated assumptions, including full-balance and final-unit requests.

The Lean proof is conditional on explicit owner-history/funding/prerequisite
conditions. Their establishment by every Rust owner-driver execution remains an
open universal refinement obligation. This is a protocol-level proof boundary,
separate from environmental outages. No implementation-wide theorem excluding
every protocol deadlock or unconditional recoverability claim is made. The account
contract does not extend to arbitrary collective contention or conflicting owners.

Subsequent progress repairs and component proofs are recorded in
[[owned-progress-evidence]]. The universal completion obligation remains open.

The composed initialized product theorem is now recorded in
[[owned-deadlock-proof-evidence]]. It replaces readiness premises with derived
product invariants; it does not establish universal Rust source correspondence.
