# Live Lean oracle for state-kernel fuzzing

The differential test sends generated authored inputs to two implementations:
the real Rust parser/installer/fold and a persistent Lean executable. Lean
receives no expected Rust results. Its oracle calls the same finite-table,
projection, contribution, state and threshold functions used by the proofs.
The executable causal-freeze evaluator is proved equal to `StateLVar.freezeRead`,
including exact cuts, exclusions and unioned raw/freeze fault evidence.

From `lean-cbcl/`, build once:

```sh
lake build cbcl-state-oracle
```

From the repository root, run the CI-sized campaign:

```sh
PROPTEST_RNG_SEED=380038 PROPTEST_CASES=512 \
  cargo test -p cbcl-parser --test state_kernel_oracle -- --ignored --nocapture
```

For a larger campaign, increase `PROPTEST_CASES` and change the seed. Proptest
shrinks mismatches and persists their seeds in
`crates/cbcl-parser/tests/state_kernel_oracle.proptest-regressions` and the
corresponding `state_freeze_oracle.proptest-regressions` and
`state_nested_oracle.proptest-regressions` files. The failure
report includes the complete JSON request and delivery variant. Replay that
request directly through `lean-cbcl/.lake/build/bin/cbcl-state-oracle`, or rerun
the Rust test to replay saved seeds. `CBCL_STATE_ORACLE` can select an alternate
built oracle. Select the direct executable: wrappers that spawn descendants
retaining stdout are outside the harness process-cleanup contract. Each response
has a ten-second timeout; the child is killed and reaped when the test exits.

The current profile covers chain and branching finite lattices, corrupted join
cells, missing/duplicate/unknown join rows, stable and revisable integer/Boolean
projections, mixed projection rejection, simultaneous contribution matches,
scalar threshold admission and compatibility, empty histories, pending/reached
reads, top faults and attributable evidence. Directed cases independently
require pending, reached, fault and rejection outcomes, including numeric and
Boolean success. Each random case compares forward, reversed and duplicated
delivery. A separate causal-DAG profile covers no freezer, sequential and
concurrent freezers, multi-parent cuts, both policies, late writes, dependent
thresholds, raw top faults and combined fault witness sets. Directed cases also
ensure unrelated-verb fields cannot enter raw finite fault evidence. The CI
workflow builds the oracle explicitly and runs these ignored tests; a normal
Cargo run does not silently require Lean.

The `events-sum` profile adds an event map and a derived sum with independently
optional source and derived freezes. `StateExecutableObservation` proves its
map/error/presentation/freeze adapters agree with the existing semantic adapters.
The reference recomputes source values at the requested cut; Rust uses its real
scoped cache. A directed example freezes source events whose sum is 2, then
freezes the derived sum at an incomparable cut where the result must be 7.
That distinguishes a `(scope, field)` cache from a field-only cache. Both source
and derived snapshots, frozen metadata and fault propagation are compared.
Generated graphs use bounded integer amounts; this is not overflow testing.

The JSON-lines request contains `table` (named elements, bottom, top and join
triples), `projection` (null or stability plus scalar rows), `contributions`
(keyword/literal/target triples), `queries` (null or scalar alternatives), and
`acts` (numeric identity plus keyword/scalar pairs). Scalars are JSON strings,
integers or booleans. The harness translates JSON booleans to CBCL `#t`/`#f`
and preserves identity across duplicate delivery. Freeze requests add a Boolean
`freeze` policy (`true` = fault, `false` = supersede) and encode acts as
`[identity, verb, predecessor-identities, keyword/scalar-pairs]`. Identities
increase along causal edges. The oracle rejects missing predecessors,
conflicting identity payloads and repeated field keywords. Generated DAGs are
bounded; backward search is a semantic reference, not the native cost model.
Responses distinguish input errors from installation rejection and report
semantic observations.

The `events-sum` request selects `"profile":"events-sum"`, supplies the same
causal `acts`, and uses nullable Boolean `source_freeze` and `derived_freeze`
policies for the `close` and `seal` verbs. It has no finite table or queries.

Fault comparison preserves evidence membership through an injective mapping
from actual content addresses to test identities. It intentionally ignores
canonical evidence ordering, repeated evidence entries and diagnostic strings.
Frozen root identities and superseded witness membership are compared as well.
The profiles have no domains, context, resources or protocol admission; generated
DAGs are fold inputs, not a claim about protocol-valid execution. The nested
profile has one source and one derived layer; arbitrary dependency graphs are
not generated. It is a live
implementation cross-check for finite state and causal-freeze semantics,
not a proof of Rust extraction or coverage of the entire state language.

Verify that the comparison catches real implementation regressions:

```sh
python3 scripts/check-state-oracle-mutations.py
```

That command builds isolated Rust copies, verifies a passing live-oracle
baseline, then requires actual assertion failures when all matching finite
contributions are replaced by first-match behavior and when a threshold hides
its source fault. Freeze mutants ignore the causal cut, suppress the fault
policy, hide concurrent freezers or discard freeze evidence when a raw fault
already exists. Nested mutants erase the cache scope or field, use whole history
for a dependency, stop unwrapping frozen payloads, or discard inherited source
faults. It leaves the worktree untouched.
