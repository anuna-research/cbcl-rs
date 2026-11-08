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
roundtrip and absent-pin connection to installed casting are proved.

A fact can instead supply `"wrapper-params"` as a parsed parameter-list string,
such as `"(((chair @chair) (reviewer @a @b)))"`. This overrides its separate cast
and pin fields. `StateContextWrapperSyntax` recognizes exactly a bindings list,
optionally followed by `:dialect` and a checked `sha256:` lowercase-hex64 pin.
The installed-cast proof includes pin identity and malformed wrapper syntax.
For a matching-pin test, the digest consisting of 64 lowercase `a` characters
is the reference identity token: the native harness substitutes its actual
dialect hash only at that exact pin value position, while Lean maps the same
checked digest to its independent dialect token. Other pin spellings are retained.
This normalization does not prove hashing.

The `context-wrapper` oracle profile takes a `params` string and compares the
wrapper parser's acceptance before checking dialect identity. This prevents the
identity gate from concealing malformed digest acceptance. The existing context
campaign covers both this parser result and the resulting full context read.
A fact can also override its cast/pin transport with `message-wrappers`: an
outermost-first array of descriptors. A transparent or role wrapper has a `kind`
(`signed`, `envelope`, `with-limits`, `with-roles`) and a `params` string containing
a parameter list; a dialect node has `kind: "lang"` and a `name`. At most 32
descriptors are accepted. The harness encloses the simple message in these
wrappers and passes the complete text through the native parsers. The Lean side
builds the corresponding typed message projection and calls its metadata
extractor. `StateContextMessage` proves that outermost cast selection and
independent simple-thread lookup compose with installed profile/root decoding.
Malformed outer role wrappers shadow valid inner ones. Raw parameters and hash
normalization retain the rules above, with substitution confined to role wrappers.
The campaign includes fixed and generated nesting plus invalid descriptor tests.
Projection from arbitrary full native ASTs, authentication/admission and general
wire correspondence remain boundaries.

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
faults. Context mutants accept quoted account strings or duplicate roster occupants,
bypass pin grammar or identity validation, stop cast search at transparent wrappers,
mislabel fixed metadata, drop mixed-thread or opener-fork
witnesses, alter the accepted count and hide the frontier. It leaves the
worktree untouched.

The same runner includes the native admission regression
`duplicate_amount_cannot_hide_a_negative_state_contribution`. Its guard mutant
lets duplicate data keywords through R7, reproducing disagreement between
first-match shape validation and last-value state extraction. This check is a
native admission regression, separately labeled from the live Lean comparisons.

The `keyword-extraction` profile compares the combined state-shape and field
extraction path, beyond the standalone first-keyword shape projection. It takes
`params` as a tagged S-expression list, using the same tags as the shape profile.
Its campaign uses `amount` and `other` data keys and string-valued `thread`
metadata. Unknown keys reject; out-of-contract thread values are input errors;
amounts enforce native state bounds. Complete pair grammar and duplicate-data
rejection run before shape checking and amount extraction. The native harness
uses a fixed empty content/header, strict wire/message parsing, installation,
R7 state-shape validation, declared shapes and actual `Act` field lookup.

`StateKeywordExtraction` proves numeric agreement from recognized grammar,
unique data keys and actual field construction, and composes it with complete
authored sum preservation. This is a typed parameter-extraction theorem, not a
proof that every native admitted message satisfies that construction. Arbitrary
nested native values, full native AST projection, authentication and protocol
admission remain outside this campaign. Mutants changing a native numeric value
or allowing duplicate data keys are checked against the live Lean result.

The `state-render` profile checks exact emitted UTF-8 strings. Its required
`value` and `state` inputs use a closed native-value tree: `["absent"]`,
`["str",text]`, `["int",canonicalDecimalText]`, `["bool",flag]`,
`["list",items]`, `["set",items]`, `["map",keyValuePairs]`, or
`["event",signer,value]`. `state` is an ordered array of `[name,value]` rows.
Integers must be canonical signed decimals in the native i128 range; nested
values are limited to depth 32. Unknown value constructors and extra constructor
arguments reject.
Stored order and duplicates are preserved by this serializer campaign; normal
state constructors establish their own set/map invariants.

The Lean oracle runs the operational buffer emitter proved equal to a separate
declarative spelling. It returns native-value and whole-state renderings as
JSON string values. Rust compares these exact strings with `Value::render` and
`render_json`, then separately checks that native output parses as JSON. It does
not parse the rendered strings before equality. C0/short escapes, Unicode,
non-string map keys, nested events/containers, i128 extrema and nonalphabetic
clause order are covered. Native uppercase-control-hex and reversed-field-order
mutants fail this comparison despite retaining equivalent parsed objects/string
values. Formal native Rust extraction, integer-formatting correspondence and
constructor sorting remain outside this profile.

The `fault-evidence` profile accepts `freezers` and `writers` arrays of UTF-8
address aliases. At least two distinct freezer aliases are required; writer
and freezer identities must be disjoint. Duplicate deliveries within either
array are accepted. The oracle constructs independent root acts, runs executable
freeze evaluation with fault policy, maps its computed witnesses back to aliases,
and returns `rendered`, the complete canonical fault JSON string. The reason is
fixed to `concurrent freezes` in this profile.

Rust evaluates a count field with a fault-policy freeze through public `fold`.
Concurrent freezers cause writer evidence to be collected repeatedly, exercising
native sorting and duplicate removal before serialization. Exact-string checks
include empty addresses, NUL/prefix ordering, quote/bracket ordering and Unicode,
plus generated reordered and duplicated deliveries. Mutants dropping the
missing-byte sentinel or retaining duplicate evidence fail executed comparisons.
These aliases deliberately bypass identity validation: this checks evidence
presentation, not admission or content-address integrity. The associated Lean
proof composes finite freeze witnesses with canonicalization and JSON emission;
native array/word/pool refinement and reason derivation remain open.

`StateAddressDigits` proves sentinel encoding, bucket bounds, computed-width
key order and adjacent duplicate normalization. `StateAddressCounting` derives
counts, offsets, cursor bounds and collision freedom. `StateAddressScatter`
derives occurrence retention, scratch coverage, pass permutation and bucket
ordering. `StateAddressRadix` establishes equal-key secondary stability and
composes the reversed-digit passes into complete lexicographic ordering and
exact fault JSON bytes without supplied sorter-correctness premises.

The live profile executes operational radix sorting, destructive source-pool
moves and adjacent duplicate removal directly; reference merge sort does not
clean up its output. Evidence occurrences form distinct pool slots, including
repeated address strings. Derived index permutation preserves bounds and ensures
every checked take succeeds without consuming a slot twice. Native usize, address-pool representation and literal Rust refinement remain open;
word bounds in the arithmetic model require a representable input length.


The compiled operational radix oracle uses `StateAddressPool`, including the
`StateAddressWords` sorter:
`USize`-valued count/prefix/next/scratch arrays proved equal to the Nat-array
and original functional semantics. Every destination bound is derived from the processed-prefix
invariant, and initial scratch contents do not affect readback. The finite
byte-key domain is checked; generic inputs retain the original behavior.
The response deadline remains ten seconds. A failed transport poisons the
session, preventing proptest shrinking from comparing a late reply to a newer
request. Its regression queues a late reply after failure and verifies that it
remains unread; disabling either poisoning or its guard fails that regression.


Word arithmetic encoding is modular in general. Exact decoding is proved from
the total-length and source-index bounds, with each scatter destination derived
from its operational prefix. The checked word path enforces those bounds before
execution, preserving the generic Nat semantics outside that domain. Lean array
and loop indices still use Nat; complete native control-loop and literal Rust correspondence remain open.


`StateAddressPool.faultBytes_refinement` covers a concrete finite address array
through word sorting, destructive checked moves, normalization and exact JSON.
The source-pool callback boundary is discharged in this model: no caller supplies
lookup success, an output permutation or an ordering certificate. Native control
indices/loops and literal Rust correspondence remain explicit boundaries.


`StateAddressControl` refines source-index iteration to USize-valued count/scatter
loops and performs native in-place prefix updates at positions 1–256. Its table
and subtraction proofs compose to `controlSort`, which the finite source-pool
sorter now calls directly. Native outer-range execution is established below; literal Rust
correspondence remains open. The live native profile asserts that valid fold
inputs do not panic, so malformed prefix-index mutations fail an executed
assertion as well as ordering/equality mutants.


`StateAddressRange` closes the modeled outer digit-range boundary. Its actual
USize cursor stops at zero and yields each exact predecessor, with termination
proved from the decoded cursor rather than an external fuel assumption. Decoded
positions equal the reversed half-open range; folding the native passes refines
the complete sort. The finite source-pool driver executes this path directly.
Literal Rust extraction and wider kernel correspondence remain open.

`StateFreezeRendering.frozen_serialized` extends exact serialization to frozen
observations. It derives the exclusion enumeration from the executable freeze
read, proves that enumeration is a sublist of the accepted scope, and derives
unique exclusion names from the scope's explicit unique-address premise. The
operational wrapper uses the proved address-pool sort and JSON emitter for the
`frozen`, `superseded`, and `value` fields. It does not add deduplication to the
native wrapper: duplicate delivery must already have been normalized in the
accepted scope. The payload and address projection remain explicit inputs; this
theorem does not establish their extraction from native acts. The `frozen-wrapper` live profile exercises this composition against native
`fold` with a count field and supersede freeze policy: predecessor writers
supply the captured value, outside writers supply exclusions, and address
aliases exercise raw UTF-8 ordering. Directed cases include an empty exclusion
set and duplicates. The required `descendants` boolean selects concurrent
writers or direct descendants that cite the freezer; both remain excluded.
Directed cases exercise both topologies, and generated cases select either
topology before reversing and duplicating writer deliveries.
Comparisons retain exact JSON strings. The profile rejects overlapping freezer,
predecessor and independent-writer identities before interpreting the history.
It remains a below-admission profile, separate from content-hash identity and
sealed-cast binding. Native root, exclusion-order and captured-value mutations
are covered by the mutation runner.

The `resource-decrement` profile exercises
[[SPEC-038-lvar-state-kernel#REQ-3808]] and
[[SPEC-038-lvar-state-kernel#TEST-3806]]. It compares the native bounded counter with
`StateResourceVerifier.observe`, including preflight, budget traversal and
aggregate finalization. It fixes the checked account configuration from the
resource proof fixture: treasury has 1000 rights and Alice and Bob have none.
Inputs choose one decrement amount, its signer, and whether the cast root and
initializer are present. Native messages carry the corresponding escrow and
causal links; Lean constructs the independently recognized typed facts. Missing
root/initializer histories are intentional pending cases below protocol
admission. Amounts are signed 64-bit wire integers and signer choices form a
closed fixture dictionary.

The comparison checks pending/fault status, complete fault witness membership,
and, for ready results, exact value and all account balances. Native histories are also reordered and delivered
twice. Directed cases cover integer extrema, nonpositive amounts, exact budget,
overspend and unknown accounts; generated inputs mix arbitrary wire integers
with values around the authorization boundary. The profile compares evidence-array bytes but does not establish general
multi-operation, transfer, ceiling, certificate-runtime, native metadata-extraction
or admission correspondence.
The mutation runner checks zero-amount acceptance, rejection of exact-budget
spends, and decrement arithmetic that credits rather than debits rights.

The `resource-graph` profile extends that fixed configuration to a treasury
transfer funding an Alice decrement. Inputs choose both signed wire amounts,
whether the funding act is present, whether the spend names it as a dependency,
and whether a distinct Alice decrement forks from the same opener. The fork
shares the declared funding dependency when present; it is not made harmless by
an independent insufficient-budget failure. Native fork messages have a distinct
nonce, while the recognized facts carry a distinct identity.

Both implementations evaluate the actual dependency graph. Directed cases cover
missing funding, present-but-undeclared funding, exact and insufficient funding,
nonpositive amounts and funded owner forks. The complete verifier supplies the
Lean result; no expected status, balance or certificate enters the request.
Ready balances, statuses and complete fault witness membership are compared
after native reorder and duplicate delivery. Mutations suppressing the owner-fork check and dependency-tip credit
must fail executed comparisons. This is a two-operation fixture with an optional
fork, not general graph, ceiling, complete fault-reason or admission correspondence.

`StateResourceRendering.witnesses_realize` proves an executable enumeration of
the complete contextual resource witness set: present relevant facts and present
context named by relevant facts' causal, owner-previous or dependency links.
Unsupported profiles retain empty evidence. The enumerator does not require a
caller-selected support or an ordering certificate. `certificate_serialized`
composes the concrete resource cause, actual verifier classification, witness
enumeration and proved address-pool renderer into canonical fault JSON.
Diagnostic reason and address encoding remain explicit representation inputs;
interpreting encoded names as distinct identities requires an injective encoding.

Both live resource profiles compare those executable witnesses with native
fault evidence in two independent representations. Native hashes are translated
to fixed recognized fixture IDs, then sorted without deduplication. The harness
rejects witnesses naming absent acts and duplicate native witnesses. Separately,
it renders the evidence value produced by `escrow::Outcome::value` directly
and compares its exact bytes with
`StateResourceRendering.evidenceBytes`, whose canonical rendering theorem is
`evidence_bytes`. Native diagnostic reason text remains outside this comparison.
Mutations deleting contextual fact retention or evidence deduplication fail
executed comparisons, as do mutations adding JSON whitespace or reversing the
native evidence array even though logical witness membership is unchanged.

The resource request's `addresses` field is a list of `[id, name]` rows generated
from the source acts, before observing their result. It carries neither expected
witnesses nor a native outcome. The recognizer requires unique nonnegative IDs,
unique string names, and exactly the accepted fixture's identity coverage.
Missing, extra, duplicate, conflicting-name and malformed rows are rejected
before verifier evaluation. The fixed lookup projection is total on every
accepted identity, and all enumerated witnesses come from that source set.
This dictionary is an explicit representation boundary, not a content-hash or
wire-extraction proof.

`StateResourceRendering.serialized_fault_persists` starts with an actual emitted
fault string. With a fixed configuration and address representation, adding
immutable accepted facts produces another serialized fault and retains every
previous canonical witness name. The proof derives fault classification from the
actual emitter result, derives a resource cause from the complete verifier, and
extends that cause to the larger accepted set. `witnesses_grow` and `names_grow`
connect contextual evidence inclusion to executable enumeration and canonical
presentation. Diagnostic reasons may change; the theorem does not assert equality
of whole fault strings across growth.

Every directed and generated resource-graph case also evaluates a larger history
that includes the funding act and the competing owner branch. Both observations
are independently compared with Lean, source-address rows are checked for
inclusion, and an earlier fault must retain its status and every earlier witness.
The growth step changes inclusion flags only, preserving existing source acts.

The resource graph also accepts optional boolean `context` and `cited_context`
flags, defaulting to false only when absent. The former includes a non-resource
core `tell` act; the latter makes the funding transfer cite it causally. These
are oracle transport controls, not dialect keywords. Present nonboolean flag
values are rejected before observation.

`resource::cited_context_evidence_matches_lean` exercises all presence/citation
combinations and generated funding/spending graphs. A present cited context
identity enters the fault witness; an absent citation and an unrelated accepted
context act do not. The native contextual act is outside the resource projection
but remains visible to the accepted-identity lookup. Lean retains its typed
non-resource fact for the same contextual-evidence selection. Both raw evidence
bytes and fixed-ID membership are compared, including growth and duplicate
replay. This remains below admission; intentionally absent cited context is not
claimed to be a causally closed protocol-admitted history. Mutations deleting
causal-context retention or reporting absent cited identities fail executed
assertions in this suite.

The `resource-freeze` profile composes the same complete resource verifier with
`StateExecutableFreeze.read`. An installed freeze declaration seals `coins` at
the funding `pay` act; required boolean `fault_policy` selects fault or supersede
handling for outside contributions. The full-history verifier supplies raw fault
witnesses to the common freeze read, which combines them with freeze conflicts.
For a healthy frozen read, the evaluator runs the complete verifier on facts
selected by the actual causal cut. The unbounded fixture's ready resource value
uses native ordered map keys and balances; `StateFreezeRendering.emitFrozen`
then emits the full wrapper, root and sorted superseded identities. An unexpected
non-ready cut is an oracle error, not a fabricated frozen payload.

`resource::resource_freeze_matches_lean` installs both policies through the native
registry. Directed cases establish that a valid late spend is excluded from the
captured resource value under supersede policy; fault policy instead reports the
freezer and late-spend witnesses. An overspend remains a raw resource fault under
both policies. Generated cases also cover funding presence, declared dependencies,
forks and cited non-resource context, with source-preserving growth and duplicate
replay. Frozen output comparisons retain exact wrapper bytes; fault output compares
complete witness membership and evidence-array bytes. Malformed policy values are
rejected with an otherwise valid source dictionary. Mutations hiding full-history
faults, discarding raw witnesses during conflict union or ignoring the causal cut
fail executed comparisons. This fixed-profile composition does not establish
general installation/AST extraction or diagnostic-reason correspondence.
