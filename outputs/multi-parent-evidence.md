# Multi-parent collective counter: Lean evidence

Contract: [[SPEC-029-multi-parent-counter-model]]. This implements the numeric DAG
protocol and its executable model, while leaving the Rust protocol unchanged.
Source: `lean-cbcl/LeanCbcl/ConsensusFree/MultiParent.lean`; scenarios:
`lean-cbcl/MultiParentAudit.lean`.

## Mechanism

```text
            A --\
           /     \
    root          M --> N
           \     /
            B --/

    local adoption: current belongs to M.parents
                    every own historical signature ID belongs to M.held
                    all evidence survives the move

    M.allowance = genesis + unique verified credits
                          - unique held costs
                          + unique cancellation refunds
```

This replaces the single-successor checkpoint selection rule for the new model.
There is no checkpoint decision quorum, winner selection, global spending oracle
or consensus fallback. Validators can independently occupy different branches and
adopt a covering merge. Parent allowances are never added.

Transaction certificates still need `2f+1` signatures among `3f+1` validators,
with at most `f` Byzantine validators. Honest local unreleased charges obey
`(2f+1)*signedCost ≤ (f+1)*versionAllocation`. The fixed-version double-counting
lemma is reused from the existing verified arithmetic.

Quorum intersection and immutable local lineages prove that versions containing
certified spending are ancestry-comparable, even though locally adopted versions
form a DAG. Full own-history coverage forces every earlier certified debit into a
later certified version, including a certificate assembled after adoption.
The maximal finalized version is a proof witness only; no validator selects it.
Unique-ID books plus cancellation/effects exclusion and local capacity then bound
all finalized debits by actual genesis capacity and finalized credits.
This orders neither individual transactions nor their effect delivery globally.

## Checked claims

- `step_invariant`, `run_invariant`: guards preserve known-manifest validity,
  append-only journals, local ancestry, complete historical coverage, effect/fence
  discipline, verified authorization and independent local capacity.
- `certified_comparable`, `certified_coverage`: derive certified ancestry and
  coverage of old reservation certificates.
- `resource_nonnegative`: derives nonnegative business resource observations;
  nonnegativity is never an endpoint assumption or signing guard.
- `finite_refinement`, `infinite_refinement`: each concrete step stutters or
  executes an authorized, funded business action.
- `release_future_safe`: cancellation-backed local release excludes future
  finalization along every continuation.
- `perform_sound`, `execute_sound`: executable guard checks generate actual
  protocol steps and runs, linking scenarios to the safety theorems.

Only standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` occur in the
new capstones. No `sorry`, custom axioms or `native_decide` were introduced.

## Execution and adversarial evidence

Run from `lean-cbcl`:

```sh
lake build
lake env lean --run MultiParentAudit.lean
```

Run from repository root:

```sh
python3 proofs/validator-budget/check_multi_parent_mutations.py
scripts/check-axioms.sh
scripts/check-verified-by.sh
```

Recorded results are `outputs/multi-parent-build.log`,
`outputs/multi-parent-audit.log` and `outputs/multi-parent-mutations.json`.
The executable audit checks split A/B adoption followed by a genuine shared M,
spending after merging, delayed old certificates, refund-backed reclamation with
old signatures retained, shared debits/credits counted once, and crowded branches
that join only after cancellation. It rejects incorrect books, summed parent
allowances, omitted histories even after release, uncertified credits/refunds,
unauthorized actions/cancellation, unbacked releases, premature effects, sibling
adoption and an isolated scaled-budget violation. The old partial-renewal example
first obtains all old reservation certificates, then demonstrates rejection of
the unsafe handoff that recognizes only one old obligation.

Mutation results come from actual executable assertions against temporary
interpreters, with the original source untouched. The control passes. Removing
historical coverage, exact books, direct-parent adoption, cancellation-backed
release or scaled capacity makes kernel `decide` assertions false. Missing
imports and unrelated type failures cannot satisfy the mutation checker.

Fresh comprehension and independent cross-model review accepted the documented
scope: [[multi-parent-orientation-review]], [[multi-parent-adversarial-review]].
The reviewer identified and rechecked the scope restrictions and isolated budget
test. The implementing coordinator records this evidence without impersonating
the reviewer in Elephant.

## Boundaries and outstanding integration

The configuration has a fixed finite universe of version/transaction identifiers.
Infinite refinement means infinitely many asynchronous steps in that universe;
it does not prove extension by indefinitely fresh identifiers. Gross fundedness
requires per-coordinate disjoint debit/credit (`Config.disjoint`). Nonnegative
resource vectors alone do not prove gross-debit affordability for net-zero actions.

Authorization booleans are verified ideal-policy results, not untrusted request
claims. Certificate-guarded transitions abstract verified message delivery.
The interpreter knows the proof-only honest partition to overapproximate Byzantine
behavior; validators cannot implement that classification. The shared `known`
cache abstracts validated evidence rather than consensus decisions. There is no
packet-level DAG refinement, concrete signature proof, growing-catalogue theorem,
coin adapter extraction or Rust implementation of this new protocol yet. The
coordinator owns these follow-on integrations. Existing single-parent actor and
Rust proofs are not silently reused as DAG equivalence claims.

Convergence is possible but not guaranteed. Incompatible outstanding proposals
can require owner cancellation; insufficient credit or missing cancellation can
stall a join. Durable honest journals and fully bound identifiers/signatures remain
assumptions. Production security/domain review is outside this library-model work.

The repository-wide Batteries linter still reports findings in unchanged modules;
the new MultiParent module has no findings after documentation repairs. The
specs-only zetl check still reports existing dead links and the new output-page
references outside its scan root. Output-page vault integration remains a
coordinator-owned backlog. Neither global lint nor vault cleanliness is claimed.
