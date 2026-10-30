---
title: Asynchronous validator-budget refinement — refutation
mode: explanation
---

# Asynchronous validator-budget refinement — refutation

The requested safety refinement is false for the current executable model.
[[SPEC-021-validator-budget-model#BUG-2100]] records a valid finite schedule in
which 33 rights finalize from an initial 30. A theorem proving all such executions
preserve nonnegative finalized rights cannot hold without changing the model.

The mathematical fixed-checkpoint result remains valid. Its cumulative per-witness
capacity premise is not preserved by partial renewal. The reconciliation identity
also remains true throughout the failing trace; retained reservations alone do not
establish the global safety property.

## Reproduce

```sh
python3 proofs/validator-budget/async_counterexample.py
cd lean-cbcl
lake env lean LeanCbcl/ValidatorBudgetRefutation.lean
lake build
cd ..
bash scripts/check-axioms.sh
```

The Python command deliberately succeeds when the counterexample reproduces.
Its JSON says `asynchronous safety refuted`; it catches the model's diagnostic
`negative finalized rights` assertion after the final effects threshold is reached.
This is not an input rejection or an intentionally weakened mutation. All owner,
context, membership, version, capacity, funding and effects guards pass.

The command includes the variant where witness 0 refuses the negative update.
Only witnesses 1,2,3 adopt the new version and all honest free budgets stay
nonnegative. D still certifies and the late A/B certificates still finalize.
Thus refusal of negative reconciliation and plain quorum version acknowledgment,
even together, do not repair this execution. D never needs witness 0's signature.

## Formal claims

The Lean module implements a fixed payment-only fragment of the reference model.
All payments use the same authenticated owner, source, recipient and genesis;
amounts are positive and transaction identities distinct. The executable commands
check local capacity, current version, exact signing certificates, finalized C
coverage, executed C dependency for D, and effects thresholds over distinct slots.
No recovery, cancellation or fence affects either trace.

| Theorem | Meaning |
|---|---|
| `guarded_trace` | Every command in the original trace returns success |
| `old_certificates` | A/B/C each have a signing quorum; honest budgets reach zero |
| `partial_update_budgets` | Renewal produces [-20,10,10] |
| `all_final`, `final_quorums` | All payments reach their signing and effects thresholds |
| `overspent` | The finalized source balance is -3 |
| `nonnegative_adopters_trace` | The variant also passes all guards |
| `quorum_adopted_partial_update` | Three witnesses adopt the partial update in that variant |
| `nonnegative_adopters_overspent` | Refusing the negative update still ends at -3 |
| `no_funded_refinement` | The endpoint is unreachable in the independent funded-payment specification |

The guarded-run theorems prevent the `getD initial` definition from masking an
invalid step. The business machine permits funded positive payments and internal
stuttering, and its nonnegative-balance invariant follows by induction. This
excludes refinement under the intended finalized-balance observation. It is not a
claim that every imaginable abstraction is refuted, nor a machine-checked
Python/Lean correspondence theorem.

## Independent review

Fresh-context cross-model reviewer `async_counterexample_review` reran both Python
schedules, compared JSON with the saved trace, compiled the Lean refutation and
checked every relevant guard mapping. The reviewer found no material correctness
issue. It confirmed only one Byzantine witness is needed and that cumulative charges
at honest witnesses 1 and 2 reach 69 against the original capacity 60.

The reviewer also confirmed the stronger nonnegative-adopter variant. Its audit notes harmless representational differences. The Lean fragment creates
the version-known flag during the first update and rejects repeated update commands.
Neither difference affects the exhibited traces. This independent guard audit is
not presented as an extraction theorem.

## Repair obligation

[[SPEC-021-validator-budget-model#CON-2102]] requires an authenticated, consistent
cut that preserves every finalized old operation and accounts for any operation
that can still finalize. Omitted consumption needs continuing capacity reservation
or enforceable cancellation evidence. An owner-provided partial history or a timeout
cannot supply that property. The no-commit branch cannot cancel an entire old
version after C has finalized.

Elephant leaves `budget-async-refinement` uncompleted and records the counterexample.
The next task is `sealed-checkpoint-design`. No certification runtime is introduced
or enabled, and the existing host-gated escrow implementation is unchanged.
This finding is about our adaptation; no external paper's complete protocol is
claimed refuted by this evidence.

Fresh-context reader `async_refutation_orientation` received only the Orientation
text. It correctly identified the refuted asynchronous claim, the continued validity
of the conditional earlier theorems, the insufficient negative-budget fix and
[[SPEC-021-validator-budget-model#CON-2102]] as the unimplemented repair gate.
