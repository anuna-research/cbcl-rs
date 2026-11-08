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
`state_nested_oracle.proptest-regressions` files, plus
`state_context_oracle.proptest-regressions` for context reads. The failure
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
integers or booleans. The finite profile also accepts `["symbol", "p0"]` in
message fields and contribution/projection literal positions. Its bounded token
grammar is `[a-z][a-z0-9_-]*`; queries retain the scalar-only input contract.
The Rust harness emits a real strict-parser symbol. Lean retains an opaque
non-scalar value, which `row_literal_not_list` and `row_ignores_opaque` prove
cannot match a verified scalar contribution row. Thus bare `p0` cannot trigger
a `"p0"` row. Authored symbolic row/projection values are rejected by installation.
This is a finite-profile comparison adapter, not a general symbol decoder or
admission check; structured message values remain outside this input contract.
Other profiles retain their existing scalar contracts. The harness translates
JSON booleans to CBCL `#t`/`#f` and preserves identity across duplicate delivery. Freeze requests add a Boolean
`freeze` policy (`true` = fault, `false` = supersede) and encode acts as
`[identity, verb, predecessor-identities, keyword/scalar-pairs]`. Identities
are independent of causal order. A bounded Kahn pass proposes an order, then
independent coverage/edge checks construct the separate causal-rank premise.
Rank compression proves history-length search fuel sufficient without changing
addresses or delivery order. The oracle rejects missing predecessors, cycles,
conflicting identity payloads and repeated field keywords. Generated freeze IDs
deliberately decrease along causal edges. DAGs are bounded; backward search can
revisit shared paths exponentially and is not the native cost model. Checker
soundness and completeness for content-consistent, separately ranked histories
are proved. Recognition is invariant under reordered and duplicate delivery.
This rank check concerns present edges; missing predecessors are rejected by the
separate closure check before it.
Responses distinguish input errors from installation rejection and report
semantic observations.

The `events-sum` request selects `"profile":"events-sum"`, supplies the same
causal `acts`, and uses nullable Boolean `source_freeze` and `derived_freeze`
policies for the `close` and `seal` verbs. It has no finite table or queries.

The `context` profile executes `StateExecutableContext.read`, proved equal to
`StateInstalledContext.nativeRead`. It covers every supported dialect, thread
and observation path, role declarations and sealed occupants, membership
threshold admission/results, and context/snapshot schema markers. Directed
histories cover absent roots, malformed or incomplete casts, duplicate roles
and occupants, invalid singleton cardinality, wrong or malformed pins,
conflicting roots, mixed thread IDs and concurrent openers. Combined failures
compare the complete union of attributable witnesses. Random histories also
vary rosters, graph structure, aliases, paths, queries and delivery order.

Context requests contain `"profile":"context"`, an authored `name`, a `path`
array, an optional string `query`, and `facts`. Each fact contains numeric `id`,
`verb`, authenticated `signer`, predecessor IDs in `parents`, nullable `thread`,
nullable `cast` (role/account-list pairs or the string `"malformed"`), and
nullable `pin` (`"correct"`, `"wrong"` or `"malformed"`). The fixed dialect
has singleton `chair`, indexed `reviewer`, and an `open` opener. Lean request identity and
closed-graph checks reject conflicting repeated facts or absent predecessors.
The same independently checked causal-rank witness rejects cycles without
requiring IDs to increase. Generated context IDs deliberately decrease along
edges. Rust constructs messages by dependencies and restores requested delivery
order, preserving all IDs and duplicate deliveries.
The serializer enumerates roster/frontier support from input facts; support
completeness is a profile boundary rather than a separate proved theorem. It errors
if a value exceeds its explicit depth bound; it does not silently truncate.

The context profile also accepts a cast as `{"syntax":"((chair @chair) (reviewer @a @b))"}`.
The Lean parser recognizes this text before `StateContextCastSyntax` checks the
binding grammar and the installed context gate checks cardinality, completeness
and duplicates. Quoted roles/accounts and keyword keys are rejected as cast
metadata. Unparseable text is a transport input error. The Rust side embeds the
same raw cast in an actual wrapper and uses the strict parser. The grammar
roundtrip and absent-pin connection to installed casting are proved; wrapper
traversal and general metadata extraction are still boundaries.

The Rust context harness builds actual content-addressed messages and calls the
strict S-expression parser, native message parser, installer and fold. Dialect
pins use the quoted `:dialect "sha256:<hex64>"` form. Existing typed-symbol pin
callers remain supported; the lexer alphabet and canonicalization are unchanged.
BUG-006 remains open for envelopes and suite-qualified keys, while context pins
now cross the real wire parser. Canonical dialect/body hashes and act addresses
are mapped to independent reference tokens only on exact equality. Hash
correctness, a formal parser-extraction proof, cryptographic signature
verification and protocol admission remain outside this profile. Fault
reasons and presentation order remain outside the comparison. Context under
freeze, domains and arbitrarily composed dependencies remains outside this
context campaign; the native context tests cover some of those combinations.

Fault comparison preserves evidence membership through an injective mapping
from actual content addresses to test identities. It intentionally ignores
canonical evidence ordering, repeated evidence entries and diagnostic strings.
Frozen root identities and superseded witness membership are compared as well.
The finite and event profiles have no context. All profiles exclude application
domains, resources and protocol admission; generated
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
faults. Context mutants accept quoted account strings or duplicate roster occupants, bypass pin validation,
mislabel fixed metadata, drop mixed-thread or opener-fork
witnesses, alter the accepted count and hide the frontier. It leaves the
worktree untouched.
