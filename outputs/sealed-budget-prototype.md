# Sealed budget checkpoint experiment

[[SPEC-022-sealed-budget-checkpoints]] defines a separate repaired symbolic profile.
The original unsafe model and its counterexample remain unchanged.

The original triangle reserves A/B/C's full 30 rights. Its successor allocation is
zero, so D cannot certify. Delayed A/B certificates still settle safely. A separate
test completes an old certificate after checkpoint installation at other witnesses.
Repeated checkpoint installation cannot reset a spent epoch journal. Conservative
unfinalized reservations cannot be cancelled by this prototype.

Run `python3 proofs/validator-budget/check_sealed.py` for repaired tests and isolated
mutants. `outputs/sealed-budget-checks.json` captures the result and failing mutant
assertions. Mutations accept wrong cut accounting, allow signing after sealing,
allow two successor votes, and duplicate credited amounts. All are caught by
executed behavioral assertions. Run the old `async_counterexample.py` separately:
it must still reproduce the unsafe model's negative balance.

Independent review: `/root/sealed_review` (gpt-6-astra, fresh context) found and
corrected quorum-install ordering in a test and exact integer/report recognition.
The fresh Orientation reader predicted delayed settlement and conditional progress.
Review also narrowed progress to one coherent proposal without competing vote
solicitation, available payloads, and per-operation witness affordability.

Lean builds local guarded-spending and freeze induction, honest quorum intersection,
and conditional uniqueness, coverage and accounting lemmas. Central axiom audit
passes with standard permitted axioms. An isolated Lean mutant removes the signing
affordability premise and fails the spending-bound proof; its compiler output is
recorded in `outputs/sealed-budget-lean-mutation.json`. Full `lake build` passes.
Vault-wide zetl validation reports existing dead links; it is not a clean gate. Signed operation sets, report snapshots,
vote/install transitions and their composed lifecycle invariant remain unproved;
see [[SPEC-022-sealed-budget-checkpoints#Evidence and remaining proof obligations]].
This experiment does not establish full asynchronous refinement, crash durability,
cryptography, cancellation, Byzantine reliable dissemination or a production profile.
