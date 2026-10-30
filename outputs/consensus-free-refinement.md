# Consensus-free asynchronous refinement

[[SPEC-025-consensus-free-refinement]] implements an executable Lean protocol and
proves its asynchronous safety refinement. It retains independent local signing
budgets. There is no consensus service, serialized reservation ledger, global
available balance or winner-selection oracle.

```text
                          independent witnesses
                         +---------------------+
owner operation -------->| local epoch budget  |----> operation certificate
                         | charge before sign  |                |
                         +---------------------+        effects certificate
                                  |                            |
                             seal journals              business operation
                                  |
                        complete cumulative manifest
                                  |
                         vote once per parent
                                  |
                        checkpoint certificate --------> local installation
                                  |
                      conflicting proposals may stall

cancellation fences ----> cancellation quorum --------> release local charge
                                  |
                      include refund in later manifest
```

Each honest signature charges `(2f+1) * cost` against a fixed `(f+1) * allocation`
for that epoch. Certificates require `2f+1` distinct witnesses from a `3f+1` roster,
with at most `f` Byzantine witnesses. Double counting bounds all finalized spending
in an epoch, not merely one operation or one chosen signing quorum.

Sealing permanently stops fresh signatures in that journal. Every later checkpoint
carries all reported candidates, including unfinished and locally released ones.
Any old certifiable operation intersects the sealing quorum at an honest signer;
its frozen report therefore preserves the operation. The proof covers certificates
assembled or delivered after the successor is installed.

Honest validators never issue both effects and cancellation fences for one operation.
A cancellation quorum excludes every past or future effects quorum. Only that proof
can release an existing local charge. The immutable signature remains recorded.
Refunds in later checkpoints are cumulative ID sets, so repeating the same refund
across descendants does not add capacity again.

The original 30-rights counterexample is repaired:

| Event | New epoch rights allocation | Final source rights |
|---|---:|---:|
| A/B/C each certify 10; only C finalizes | — | 20 |
| Complete checkpoint holds A/B/C | 0 | 20 |
| D tries to certify another 3 | 0; honest signatures rejected | 20 |
| Delayed A and B finalize | 0 | 0 |

A separate regression cancels A instead, carries its refund into a descendant,
spends 3 in the new epoch and finalizes delayed B. The source ends at 7; A cannot
finalize. Another fills an honest local budget with X, cancels X, reuses that budget
for Y, then advances through repeated refund manifests without inflation.

The account/depth archive is proof bookkeeping for certificates that already exist.
Registration overwrites unconditionally after certificate validation. The proof
shows any existing value must be identical using parent certificates, honest
vote-once journals and quorum intersection. It does not use a first-writer guard.
The ghost frontier appears only in bookkeeping and the safety proof, never in
operation admission. Split proposals can leave every candidate uncertified.

The generic proof modules are:

- `ConsensusFree/Core.lean`: local guards, immutable manifests and certificate events.
- `Archive.lean`: same-slot equality, permanent records and hole-free known history.
- `Evidence.lean`: honest signature/effects/fence/proof provenance from genesis.
- `Capacity.lean`: local charge bounds and aggregate epoch consumption.
- `Coverage.lean`: old-certificate coverage, exact cumulative books and nonnegative resources.
- `Execution.lean`: executable command soundness and funded finite/infinite refinement.
- `Currency.lean`: typed mint/burn/pay/headroom semantics, issuer policy, conservation and bounds.

`full_async_refinement` maps every executable finite command schedule to independent
funded business steps after removing stutters. `infinite_async_refinement` proves
invariant preservation and stepwise simulation for infinite executions, without
fairness or termination. `released_never_finalizes` rules out late finality following
honest local release. Funding and resource bounds are derived from genesis and all
protocol transitions; no endpoint safety or global spending bound is assumed.

Reproduce the checks:

```sh
python3 proofs/validator-budget/check_consensus_free.py
```

The runner builds the canonical model, executes the main and independent regressions,
compiles a clean isolated dependency-tree baseline, and rejects mutated budget,
seal, vote-once, cancellation, manifest and certificate guards through their dependent
proofs. Recorded evidence is `outputs/consensus-free-checks.json`. From `lean-cbcl`,
`lake build` checks the whole library. From the repository root,
`bash scripts/check-axioms.sh` audits theorem dependencies.

Fresh-context cross-model review by `/root/consensus_free_design_review` (gpt-6-astra)
found no blocking safety defect or hidden ordering oracle. It checked the invariant
induction for circularity and independently ran typed currency and adversarial
checks retained in `outputs/consensus-free-independent-review.lean`. The Orientation
reader correctly distinguished consistent certification from consensus termination.

Cryptographic authentication and durable honest journals remain explicit environment
assumptions. Archive/journal predicates abstract supplied authenticated evidence,
not shared runtime lookups. The executable adversary model knows an arbitrary
honest core; actual validators do not identify which peers are honest. Operation,
checkpoint, account and resource universes are finite typed parameters of arbitrary
size; dynamic wire ID allocation and Rust/network/storage correspondence are not
mechanized.

Fences are validator-internal actions. The safety model permits preemptive fencing
and does not prove an owner-cancellation request policy. A host can strengthen that
guard with owner authorization. Split execution/fence votes, split checkpoint votes,
overloaded manifests and Byzantine withholding can stall; no forced recovery service
resolves them. The proved ceiling is floor plus genesis rights and headroom; binding
an externally declared cap to those allocations remains an initialization obligation.

The rejected serialized-ledger shortcut is documented in
[[SPEC-024-asynchronous-reservation-refinement]]. The consensus-backed
[[SPEC-023-abortable-budget-handoff]] is retained as historical research and is not
imported by this profile. The original unsafe partial-renewal model remains intact
as a regression subject. No production Rust certification runtime is enabled here.
