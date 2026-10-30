# Validator-budget reference model

This is the executable companion to [[SPEC-021-validator-budget-model]], not a
production certificate API. It models symbolic authenticated messages and durable
journals in memory, with exact integers rather than floating-point fractions.

```text
proposal -> local joint reservation -> signing certificate
                                         |
                               dependency-closed execution
                                         |
                                  quorum effects evidence
                                         |
                                  finalized receipt
                                         |
                           recognized by a version update
```

Run the behavioral tests and unsafe mutations:

```sh
python3 proofs/validator-budget/check.py --output outputs/validator-budget --lean-mutation
```

Run the formal library and its audits:

```sh
cd lean-cbcl
lake build
cd ..
bash scripts/check-axioms.sh
bash scripts/check-verified-by.sh
```

`model.py` contains source/issuer authorization, local rights/headroom reservations,
portable symbolic certificates, bounded pending delivery, final effects, independent
version transitions, version merges and no-commit recovery. Recovery assumes one
abstract consensus outcome and delivers that outcome to all witnesses in a reference
action. It does not implement the commit/adopt recovery branch or consensus.

For n=3f+1 and quorum 2f+1, local witness budgets are scaled by s=2f+1. Initial
capacity is k times the account allocation, where k=f+1; signing costs s times
the operation consumption. A receipt reconciliation adds k times its resource
delta, refunding s times an own reservation only if that reservation is covered.
Uncovered signed operations remain charged. Negative free capacity is retained as
exposure rather than rounded or clamped away.

`LeanCbcl/ValidatorBudget.lean` proves fixed-checkpoint signature-capacity bounds,
the joint dimensions and fixed-checkpoint mint/burn floor/ceiling consequence,
local reservation/reconciliation identities, and effects-quorum/fence exclusion.
It also models monotonic final receipt bookkeeping. Its chosen honest core is a
proof device: an actual committee with at most f faults contains 2f+1 honest
members, even if fewer than f are faulty. Witnesses need not know that core.

The Lean capacity premise must be established for an actual history. The local
reconciliation identity does not establish that premise across asynchronously
advancing versions. The Python model is not extracted from Lean and no refinement
theorem between them is claimed. Finite schedules exercise the lifecycle but do
not prove it safe or live for every execution. The remaining proof task stays open
in Elephant under `budget-async-refinement`.
