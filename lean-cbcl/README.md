# Lean proof status

The recursive token and raw Unicode-scalar installation theorems for
[[SPEC-018-dcfl-installation]] are implemented and independently reviewed.
There is no claim of Rust parser or installation-gate equivalence.

`CBCL.FormalLanguage.DPDA` enforces finite input, control-state, and stack-symbol
types. Transitions consume one symbol and replace only the stack top. Missing
transitions reject permanently. Acceptance examines only the final control state
after consuming the complete word.

`ForestAlgebra.isRealtimeDCFL` constructs such a machine for any finite forest
algebra. `ForestAlgebra.accepts_iff` proves equivalence with an independently
defined language of serialized syntax forests, over every token word. The proof
includes malformed input and imposes no nesting bound. Its axiom dependencies
are `propext` and `Quot.sound`.

`InstalledSyntax.environmentDCFL` constructs the recogniser for each finite
installed environment. `decode_encode_atom` proves preservation of concrete
atom predicates; `encoded_direct_tree` and `recognizes_expression` connect
recognition to the independent, scope-indexed `admittedAt` evaluator. The grammar
includes recursive wrappers, nested scope replacement, declared performative
membership, recipients, and restricted keyword values.

`InstalledSyntax.dcfl_preserved_many` covers arbitrary finite append sequences.
`VerifiedFresh` identifies the existing Lean R1/R2/R3 verification conjunction
plus freshness; `pipeline_verified_fresh` connects it to `verifyDialectString`.
`verified_fresh_installations_dcfl` and `verified_sequence_unique` cover that
relation's finite sequences. Rust's additional admission gates are not modelled
as equivalent; the unconditional finite-environment theorem also covers any
finite environments selected by stricter policies.

These results use `FormalLanguage.IsRealtimeDCFL`, the finite-machine
certificate for languages of arbitrary words.

`InstalledSyntax.Raw.environmentDCFL` adds a concrete finite lexer and proves
DCFL membership for the declared raw language. Its input alphabet densely
numbers all Unicode scalars, excluding surrogates. `FiniteLexer.product_accepts`
proves composition over every raw word, including lexical failures; pending
atoms and parentheses can be processed in a single stack-local transition.
`Raw.nameMatches_word` proves exact name matching for arbitrary token lengths.
`Raw.check_correct` connects the executable checker used by tests to the actual
finite DPDA. `Raw.dcfl_preserved_many` and
`Raw.verified_fresh_installations_dcfl` provide the raw installation capstones.

The concrete lexer defines SPEC-018's lexical language. This is not a separate
formal equivalence proof against the IETF prose or existing Rust/Lean parsers.
The spec follows first-character dispatch for `--3` (a symbol), despite a
contradictory draft example. UTF-8 byte decoding, runtime conformance, expansion
costs, and causal validity remain separate obligations.

`VerifyKnowledge` lifts `verify_monotone` from the valid-is-sticky preorder to the
flat knowledge order `kle` (`verify_knowledge_monotone`):
a terminal verdict, `valid` or `violation`, is unchanged by store growth, and only
`unknown` can move (`verify_valid_stable`, `verify_violation_stable`). This is
SPEC-003 REQ-302 as stated, mirrored by `crates/cbcl-core/tests/monotonicity_tests.rs`.

`AdmissionStratification` connects the state layer (`State`) to the R6 store
language: an admission that reads one act and the accepted set's skeletons
gives verdicts no state rule can move (`admit_ignores_data`), and its store
language is regular, hence trace-DCFL (`r7Store_isTraceDCFL`). Feeding one
`count` rule back into acceptance leaves the regular class
(`countGated_not_regular`); enforcing a domain at admission breaks
valid-stickiness (`domain_feedback_not_sticky`). The Rust `admit` is checked
against this form by `crates/cbcl-parser/tests/admission_state_free.rs`, not
proved equivalent.

`StateRefinement` supplies a typed execution machine for a fixed thread,
dialect, admission function, and immutable authentication premise.
`behavior_refinement` maps its behaviors into an independently supplied business
machine, with explicit initialization and acceptance-effect obligations.
Internal steps preserve accepted history; reachable histories have unique
addresses and contain only received, authenticated acts.
`counter_behavior_refinement` discharges those obligations for the existing
counter fold using independently defined labelled integer addition and subtraction.
Examples cover child-before-parent delivery, blocked acceptance, duplicate
insensitivity, and conflicting addresses.
Infinite behaviors retain stuttering, including infinite waiting.
This proves model-level safety; Rust equivalence, deployed authentication,
fairness, and other business instances remain separate obligations.
Contract and claim boundary: [[SPEC-019-state-rules#CON-1906]].

Run `lake build` and `lake exe runLinter LeanCbcl` here to check the library,
grammar examples, and Batteries lint gate. Run
`lake env lean DCFLInstallationAudit.lean` for the exported DCFL axiom audit.
From the repository root, also run `scripts/check-axioms.sh` and
`scripts/check-verified-by.sh` to match the remaining Lean CI gates. The new
capstones use only `propext`, `Classical.choice`, and `Quot.sound`. Grammar tests
use kernel `decide`; the arbitrary-nesting property is proved by induction.

Full evidence: [dcfl-raw-installation-evidence-2026-09-10](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/dcfl-raw-installation-evidence-2026-09-10.md).


The separate multi-parent numeric protocol in `ConsensusFree/MultiParent.lean`
allows local root→A/B→M DAG adoption with full immutable signature coverage.
It proves certified-version ancestry, late-certificate coverage, nonnegative
resource vectors, finite/infinite funded refinement and safe cancellation releases.
The interpreter is a model harness over verified certificate evidence, not the
Rust wire protocol. Infinite traces range over a fixed finite catalogue; funded
refinement requires disjoint debit/credit per coordinate. It does not guarantee
progress under contention. Rust uses DAG adoption for every quorum-budget context under [[SPEC-031-unified-quorum-dag]].
Contract: [[SPEC-029-multi-parent-counter-model]]. Evidence: [multi-parent-evidence](https://git.anuna.io/anuna-research/cbcl-rs/src/commit/96d5858d427fb1e371e0a8f13ddf0b23c6c6c8f2/outputs/multi-parent-evidence.md).

Run `lake env lean --run MultiParentAudit.lean` here and
`python3 proofs/validator-budget/check_multi_parent_mutations.py` from the repository
root for executable branch joins and isolated guard mutation checks.


`MultiParentRustOracle.lean` supplies the shared Rust transition oracle and proves
`apiPerform_sound`, `oracle_run` and `oracle_safe`. Its API adapter requires source
metadata for honest transaction registration, an own signature before release,
and treats already-durable signing/adoption retries as stuttering. The abstract
protocol is unchanged. The generated catalogue/traces exercise production Rust
APIs and compare projected state after every command, with journal recovery.
These synchronized traces plus separate delayed-delivery tests establish tested
correspondence, not universal source equivalence or network refinement.

Run `python3 proofs/validator-budget/check_rust_multi_parent.py` from repository
root to regenerate the reference in memory and check the committed fixture.
Use `--write` only after inspecting an intentional oracle change.


Single-parent counter modules remain historical formal models; the Rust runtime
has no selector or compatibility path for them. Its account and collective modes
both use scoped DAG adoption. The current collective reference still applies;
account DAG transfers have execution/adversarial evidence, with their formal
extension tracked separately in [[SPEC-031-unified-quorum-dag]].

## Conditional Byzantine liveness

`ConsensusFree/Liveness.lean` extends the existing multi-parent model without
changing its transition guards. `eventual_finality` proves that an authorized,
uncancelled transaction eventually has a permanent effects certificate when:

- Each of the `2f+1` honest-core validators eventually remains able to admit its
  reservation until it signs. This is the actual `SignAllowed` guard, including
  the local active version and scaled reservation budget, not just global funds.
- Honest outstanding signing and effects work is weakly fair: a continuously
  enabled action is eventually scheduled. Requests, operation-certificate
  delivery/retries, durable writes and processing are abstracted by this premise.
- Original-actor cancellation is not authorized for this transaction throughout
  the fixed catalogue execution. Byzantine cancellation signatures remain allowed.

The execution is an infinite schedule of accepted **existing** `perform` commands.
Other validators are unrestricted by honest guards and need not contribute a
single vote. Fairness assumes scheduling of actions, never eventual signatures
or certificates. The proof obtains those conclusions:

```text
Persistent honest admission + weakly fair signing
                   |
                   v
Each honest reservation signature eventually exists and persists
                   |
        finite honest roster -> a common suffix
                   v
Operation QC exists; honest cancellation remains impossible
                   |
          weakly fair honest effects actions
                   v
Each honest effects signature eventually exists and persists
                   |
                   v
Permanent effects QC, using honest votes alone
                   |
     reliable delivery and retention of individual votes
                   v
Client eventually possesses a verified effects QC
```

`client_eventual_finality` supplies the final observation step using an `Observer`
with authentic, eventually delivered, retained effects votes.
`observed_certificate_sound` connects the observed quorum back to finality.
This is not a packet-level refinement: request and operation-QC dissemination
remain abstracted by fair action scheduling, and cryptography/physical durability
and Rust equivalence are still outside the Lean theorem. No deadline or throughput
bound follows. An attacker that permanently starves admitted honest work violates
the fairness premise; there is no unrestricted denial-of-service guarantee.

`envelope_eventual_finality` gives a concrete sufficient admission condition:
honest validators keep the transaction's active version and the sum of **all
candidate debits in that version**, multiplied by `2f+1`, is at most its allocation
multiplied by `f+1`, independently for every resource. Authorization is checked and
absence of cancellation implies no releases. This conservative envelope allows
concurrent work within its budget. The general theorem also permits version
changes after a validator has already signed. Neither statement proves that
arbitrary contention will eventually establish the admission premise.

`MultiParentLivenessAudit.lean` kernel-checks a positive infinite execution with
three honest voters and one silent Byzantine validator, including an observer
delayed by seven abstract steps. It also proves why the assumptions matter:

- A replay-only execution never finalizes an otherwise admissible request when
  scheduling fairness is absent.
- For `f=1`, a debit of 3 from a pool of 3 is globally affordable but fails the
  local admission inequality `3*3 <= 2*3`. A weakly fair execution can stall.
- Even requests individually admitted at genesis can deadlock through contention.
  With a pool of 3 and two debits of 2, honest validators can reserve as follows:

```text
                 request A    request B
honest 0             yes           -
honest 1             yes           -
honest 2              -           yes
Byzantine             -            -       withholds forever
                 ---------    ---------
votes                 2            1       quorum requires 3
```

Each honest validator has exhausted its local reservation capacity. Neither
operation QC forms, no honest effects action is enabled, and fair target-action
scheduling can legitimately replay forever. `contention_can_stall_fairly` proves
this counterexample for an actual accepted infinite execution. Perfect delivery
of the existing votes would not supply the missing reservations. Progress through
this case needs cancellation/retry or another contention-resolution mechanism;
unconditional contention liveness remains open.

Run from this directory:

```sh
lake build LeanCbcl.ConsensusFree.Liveness
lake env lean MultiParentLivenessAudit.lean
```

The capstones and countermodels use only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`). The main liveness capstones are also registered
in `AxiomAudit.lean` for `scripts/check-axioms.sh`.

## A concrete fair retry scheduler

`ConsensusFree/Scheduler.lean` provides an executable reference dispatcher and
proves its fairness. It composes with the conditional liveness results above.
The queue is a FIFO retry ring. On each completed worker turn it:

1. Attempts the head job using the existing protocol's `perform` guard.
2. Executes it if it is valid and its handler cooperates; otherwise emits a
   stuttering `replay` step.
3. Rotates that head behind the remaining queued work and the finite new arrivals.

```text
before:     [ blocked effects | sign A | sign B ]    arrivals: [ new jobs ]
                       |
                   try/skip
                       v
after:      [ sign A | sign B | new jobs | blocked effects ]
```

`position_serviced` proves that a job with `k` jobs ahead of it is tried after
exactly `k` worker turns, regardless of later arrivals. `admitted_revisited`
proves that a retained admitted job is tried again on every suffix of the run.
Total arrivals may be unbounded; each turn admits only a finite list. Duplicate
jobs are allowed. Arrivals do not overtake the existing queued occurrence.

`scheduler_fair` connects those queue facts to the **actual computed command**:
if admitted unmuted work remains enabled, the dispatcher eventually executes it.
`sign_fair` and `effect_fair` discharge the original protocol's two fairness
premises. These are proved properties, not fields assumed in the scheduler model.

`scheduled_finality` requires persistent local admission, no owner cancellation,
and `HonestJobs`: every honest sign/effects job eventually enters the queue and
its handler cooperates. `scheduled_envelope_finality` derives admission from the
explicit arithmetic envelope and fixed honest local versions. Neither capstone
takes a `signFair` or `effectFair` argument. Byzantine handlers need not cooperate.
The dispatcher uses a supplied handler policy and the existing ideal `perform`
semantics, whose core classification separates honest guards from unrestricted
Byzantine actions. The dispatcher itself does not choose an honest core.
Byzantine commands and jobs may also enter the queue.
`scheduled_client_finality` adds eventual receipt under the existing reliable
individual-vote delivery/retention assumptions.

The audit checks an effects job blocked at the head before its reservation work,
rotation to a valid signing job, finalization with validator 3's operation/effects
handlers muted, and delayed client observation. A second computed schedule begins
with an empty queue, admits the honest jobs later, and contains a never-ending
stream of Byzantine cancellation-fence jobs. The finality capstone applies without
an assumed fair schedule. The earlier reservation-contention countermodel remains
valid: retrying disabled work does not create reservation capacity.

The remaining boundaries are explicit. Natural-number ticks count **completed**
worker turns: termination of actual storage I/O, OS CPU access and request delivery
into the admitted queue are not established by this algorithm proof. The reference
queue retains jobs for retry, including already completed idempotent work; it has
no eviction, timeout or memory-capacity policy. Unbounded growth is permitted in
the model, so this is not a bounded-memory or unrestricted DoS guarantee. It is
not the current Rust runtime's queue implementation and introduces no Rust code
or host protocol selector. One reference queue models service of abstract validator
actions; a single sequence records their interleavings, not a shared ledger ordering
or consensus service. Composition of separate validator worker queues,
request/operation-QC network refinement and Rust scheduler equivalence remain
separate obligations.

Verification from this directory:

```sh
lake build LeanCbcl
lake env lean MultiParentLivenessAudit.lean
```

The queue, fairness and scheduler-finality capstones are included in the main
axiom audit and use only the same standard Lean axioms as the existing proofs.


## Explicit HLC arbitration

`LeanCbcl/HlcRegister.lean` proves soundness/completeness of greatest-candidate
selection under lexicographic physical/logical/signer/address ordering, uniqueness
under address consistency, and invariance under candidate-set equality. Separate
component theorems compose arbitration with verb, current-own and current-keyed
selections. The model consumes typed numeric evidence; the signer rank is an
order-preserving abstraction of byte order. It proves neither honest clock
generation, wire/Rust correspondence, resource finality nor a whole-clause kernel
correctness theorem. The public component theorems are in `AxiomAudit.lean`.


## Whole typed state-kernel correctness

`LeanCbcl/StateKernelClause.lean` composes independent denotations for all 16
surface heads into an arbitrary finite clause theorem. `compile_clause_complete`
accepts every independently well-formed supported clause; `whole_kernel_correct`
proves successful evaluation meets its independent surface meaning;
`well_formed_kernel_correct` combines these for unique-address accepted stores.
Domains, replacement sources, HLC/address choice, finite map support, events,
histograms, sums and established protocol progress are covered. Component map
completeness is extensional: key order and reads outside support are irrelevant.

The bounded-counter part preserves typed verifier tags and computes ready budget
observations. Verifier classification and resource-DAG validation remain outside
this proof. Parsing, installation checks, canonical rendering, clock honesty and
Rust equivalence are also separate obligations. This is denotational correctness,
not a universal business-refinement or liveness result. See SPEC-036 and
`proofs/state-kernel/state-kernel-verification.md` for the exact inventory and checks.

```sh
lake build
lake exe runLinter LeanCbcl
../scripts/check-axioms.sh
python3 ../scripts/check-state-kernel.py
```


## Conditional strong eventual consistency

`StateKernelSEC.lean` proves equal accepted sets give extensionally equal
observations for every expression and arbitrary compiled clauses. Its shared
`Context` fixes the dialect interpretation and requires causal/resource evidence
providers to respect set equality. Store merge is set union and is associative,
commutative and idempotent modulo membership; duplicate insertion preserves
observations. These merge laws do not reconcile conflicting addresses or prove
that a runtime can bypass admission when merging received data.

`StateKernelDelivery.lean` uses the existing `StateRefinement.Behavior`, including
receipt, pending candidates, acceptance, rejection, waiting and idle steps. Under
eventual receipt, continuously enabled transition fairness, finite lower-ranked
dependencies, dependency-based admission and no false rejection, it proves:

- `eventual_acceptance`: every valid act eventually enters and remains accepted.
- `eventual_dissemination`: an accepted act eventually reaches another compliant replica.
- `finite_history_stabilizes`: a complete finite history eventually equals each accepted set.
- `strong_eventual_consistency`: any two compliant replicas agree at all sufficiently late times.

Fairness schedules actual acceptance-labelled transitions; acceptance membership
is derived from `Step`. `StateKernelSECTests.lean` supplies a nonempty two-act
replica with out-of-order receipt, and an otherwise legal starving execution
excluded by fairness. A growing unique-address snapshot sequence demonstrates
that ongoing writes need not produce a final count; this is not an instantiated
infinite replica execution.

These are conditional typed-model results. Admission obligations, transport,
resource classification/finalization and Rust correspondence remain separate.
A shared evidence provider is required: two unrelated individually extensional
providers are insufficient. See SPEC-037 and
`proofs/state-kernel-sec/state-kernel-sec-verification.md`.

```sh
python3 ../scripts/check-state-kernel-sec.py
```

## LVar state kernel

[SPEC-038](../specs/SPEC-038-lvar-state-kernel.md) remains **draft**. The committed
proofs cover the following typed-model layers for the prior single-source
observation inventory. SPEC-038 v0.4 adds approved condition observations and a
sealed-root migration. Native root migration is implemented and verified;
condition implementation and extended proof acceptance remain pending.

- `StateLift` proves accepted-set lift invariance and the union/join law.
  `StateLVar` and `StateObservation` compose threshold, domain, context, resource,
  and freeze fault paths; `StateObservationPlan` combines those paths with data
  observations. Snapshots may revise; threshold answers are stable or faulted.
- `StateResourceCones`, `StateResourceFrontier`, `StateResourceCounters`, and
  `StateResourceWorklist` connect native dependency traversal and budget checks
  to exact cones. `StateResourceAggregate`, `StateResourceAccounting`, and
  `StateResourceSolvency` discharge checked aggregate arithmetic and account
  solvency before finalization.
- `StateResourceVerifier.native_verifier_certificate_iff` proves the full typed
  native fault classifier is equivalent to an accepted resource certificate.
  `native_certificate_read_refinement` connects its fault read to the exact
  certificate evidence channel. Preflight, budget verification, and aggregate
  checks are composed; classifier correctness and fault persistence are proved.
  Unsupported collective/quorum profiles have constant empty fault evidence.
- `StateInstalledCompiler`, `StateInstalledClause`, `StateInstalledLattice`, and
  `StateInstalledLowering` prove refinement and completeness of the installed
  semantic IR against independent readers. They cover backward references,
  whole-clause freeze attachment, source-relative threshold dispatch and
  admissibility, observation tags, conditional eventual agreement, and fault
  dissemination.

`StateAuthoredQuasiDeterminism.authored_quasi_determinism` assembles the complete
typed authored agreement guarantee. It covers actual emitted threshold and
same-freezer value agreement, exact equal-set observations, immediate accepted
witness replay, finite-witness dissemination, finite-history convergence and
no-top full-data SEC. `StateAuthoredFrozenAgreement` derives output/source
pairing through fresh compilation; `StateDataLocalWorld` connects normalized
local interpretation to the common causal world. Excluded metadata may grow
without changing a successful frozen value.

These results extend the resource-classifier boundary of SPEC-036/037; those
older theorems retain their stated provider premises. Concrete typed factories,
finite validators, authored context/domain binding and functional cached freeze
scopes are composed. Literal Rust AST/wire extraction, authentication,
clock/signer mapping, mutable-driver execution and universal native
canonical-renderer extraction remain explicit proof boundaries. The specification remains draft for implementation of the approved sealed-root
migration and authored product conditions. The existing typed agreement proof is
complete for its prior observation inventory; TEST-3815 extends it to conditions. Ongoing threshold preservation is also proved in its existing concrete
preservation modules.

Concrete factories now cover legacy primitives, the typed native resource
reader, closed context paths, initializer/roster domains, and finite contribution
and projection tables. `StateResourceReadEquivalence` proves equality of the
modeled pending/ready/fault read under fact permutation, including aggregate
value, rights, and headroom. `StateFiniteRead` proves upward-closed finite reads
and distinct-success conflict using actual domain-selected source state.
`StateAuthoredBindings` now combines those factories into whole-clause source
lowering, with history-independent metadata checks and observation-specific
freeze templates. `StateCompiledFreezeGrowth` reflects actual compiled error
paths and proves named fault growth and eventual dissemination while plans are
regenerated. `StateFreezeScopes` connects clear global cached cuts to nested
plan data. `StateNativeReader` proves complete functional cached plan-reader
equality, including faulted reads and nested freeze dependencies. Literal Rust
mutable-reader/cache correspondence remains open. `StateInstalledRecognition`
proves exact reference compiler acceptance; authored preparation now supplies
all metadata and reference premises, with unchanged compilation results.
`StateAuthoredCompletion` constructs concrete plans/readers from preparation
and connects them to complete functional cached-reader observations, including
faults and equality on equal accepted sets. `StateFiniteUpperCache` proves the
optimized upper-set maximum formulas and admitted scalar decoding equal the reference
finite gate. `StateFinitePairLoop` proves stored cache-vector lookups, unordered
early-exit traversal, duplicate precedence and first-error indices tied to the
original scalar queries. `StateFiniteReadCache` constructs aligned once-decoded
query arrays. `StateInstalledBounds` enforces native positive default-tightening
limits; `StateFiniteIndexBounds` proves dense lookup with exact UInt32/UInt64
offsets. `StateFiniteDenseCache` composes both backends through stored upper-set
maxima and first-pair diagnostics to the complete source-owned query compiler.
The live oracle rejects disagreement between backends before comparing with Rust.
Literal R7 extraction/integration, formatted diagnostic
strings and allocation/runtime cost correspondence remain separate boundaries. Native
missing-link lists, owner tips, diagnostic reasons and canonical serialization
are outside the modeled resource read. SPEC-038 acceptance remains partial.

`StateKeywordExtraction` recognizes complete keyword/value parameters and
checks R7's unique nonrouting-data keys before constructing typed fields.
Shape's first numeric match is proved to equal the extracted state's numeric
value; routing fields are excluded. The resulting checked amount theorem and
complete authored sum-preservation theorem consume source syntax and successful
extraction, with no independent numeric-field oracle. Native AST/admission
correspondence to this parameter/typed-field projection remains open. The live
`keyword-extraction` profile separately tests strict parsing, R7, shapes and
actual native amount lookup, including the duplicate-key ambiguity regression.

`StateJsonString` proves lossless canonical quote/escape encoding and appending
to any output buffer. `StateJsonValue` proves operational emission equals a
separate declarative spelling for every native value variant and complete state
objects, preserving stored container and clause order. `StateJsonOracle` powers
an exact-byte comparison with native `Value::render` and `render_json`; it catches
uppercase control-escape and field-order changes that parsed JSON can conceal.
Constructor sorting, Rust extraction and native integer-formatting correspondence
remain open; no root-identity change is part of these renderer proofs.

The implementation documents its current collection and freeze costs rather
than claiming strict linear evaluation: ordered collections take `O(n log n)`,
and retaining all concurrent-freeze witnesses can add `O(n f)` work for `f`
earliest freezers. See SPEC-038 NFR-3800 for the full clause/cut bounds and
separate native-validator costs.

From `lean-cbcl/`, run:

```sh
lake build LeanCbcl
lake exe runLinter LeanCbcl
../scripts/check-axioms.sh
python3 ../scripts/check-state-lift-mutation.py
python3 ../scripts/check-state-lvar-mutations.py
```

`StateMemoizedReader` proves exact scope/field memoization from an empty cache
against an independent uncached recursion, including branching requests and
shared cache reuse. Its native request body keeps dependencies at the current
scope, unwraps frozen payloads, returns faults before reading historical cuts,
and redirects each field into its own preplanned cut. `StateReaderIndices`
constructs the request ranking from successful installed-field compilation.
`StateAuthoredDependencies` derives exact dependencies from every concrete source
factory through successful preparation and source-relative resolution.
`StateScopePool` constructs the actual indexed cut pool, reuses freezer identities,
normalizes duplicate deliveries and derives active-plan membership.
`prepared_scoped_cache` combines those constructions with cache execution.
`StateReaderValues` constructs those normal/fault/wrapper operations from actual
scope data and resolved source rules. Its source, derived and complete cached
freeze adapter equations match `StateNativeReader`, including both fault witness
sets and historical payloads. `prepared_fixed_cache` needs no supplied leaf
callbacks. `StateReaderReachability` now constructs that request-domain restriction from
successful preparation: native initial reads include threshold sources, every
continuation stays within original source fields and allocated scopes, and
cache provenance excludes unsupported helper fallbacks. A non-vacuous concrete
fixture exercises the complete initial request inventory. `StateCompiledFieldEquations` now derives completed-dictionary source/derived
lookup equations and binds every normal body step to its bare compiled plan.
It proves the complete equation for fields without their own freeze, and recursive
cache/transcript equality for prepared clauses with no freezes, including faults
and threshold source reads. `StateScopeProperties` and `StateFrozenBodyEquations` now close both terminal
fault and successful own-freeze body equations. The independent recursive
reference and complete initial source-request transcript/cache equal the compiled
plan meanings for prepared clauses with freezes. Concrete fixtures cover
incomparable cuts and a prepared context/count/threshold/freeze clause.
These results require content-consistent histories with a separate causal rank.
Finite rank compression now bounds actual ancestry search by history length,
without sorting delivery or renumbering semantic addresses. Scope, cache and
output compiler proofs inherit this generalized premise.
`StateThresholdDispatch` now identifies allocated raw scopes with exact semantic
freezer cuts. `StatePreparedOutputs.prepared_cache_outputs` composes actual
empty-cache source transcripts into successful output lists using source-owned
native, factored and finite query policies. A concrete authored fixture constructs
installation and outputs; missing/extra transcript values fail explicitly.
`StateOutputCompiler` now compiles those source-owned policies to closed output
instructions capturing complete source plans and clause freezes.
`authored_compiler_refinement` constructs actual code and proves its complete
output vector equal to actual empty-cache execution plus output adaptation.
`CompiledObservation` retains the preparation history; observing a grown history
requires fresh preparation. Older generic full-history `thresholdRaw` plans are
used for source dictionary construction/checks, not emitted output semantics.
`StateCausalRank` constructs and independently checks a topological rank witness
for arbitrary delivery order. Its checker supplies the proof premise to freeze
and context oracle validators; generated labels deliberately decrease along
edges. A reversed, duplicated descending-address fixture constructs complete
authored compiler/cache outputs. `StateCausalCheckComplete` now proves that the
actual Kahn implementation constructs exact coverage and a checked unique-address
order on every content-consistent ranked history. Recognition is equivalent to
separate-rank existence and invariant under accepted-set-equivalent delivery.
Predecessor closure is independently checked by the outer validators; literal
native admission-to-rank extraction remains a boundary.
`StateOpenerLocality` derives business-opener ancestry from an executable local
predecessor check and a separate causal rank, allowing metadata roots outside
the protocol inventory. Clear initializer evidence then stays inside freezer
cuts; a healthy fault freeze preserves domain-selected history and count.
A prior count success survives growth and the historical cut. Fixtures construct
healthy evidence and reject the acyclic-but-unrooted counterexample.
Literal R5/R6 admission-to-check correspondence, multiple/context domains and
general source-policy locality remain open; R7 opener recognition alone does not
prove that interface.
Literal Rust value/graph/map/vector extraction and rendering remain boundaries. Executable cache
witnesses and focused mutations exercise aliasing, wrapper and cut mistakes.

The live [state-kernel oracle](../docs/state-kernel-oracle.md) executes the proved
finite reference functions against generated Rust installation/fold cases.
Build it with `lake build cbcl-state-oracle`; CI runs the seeded differential
property test. Its initial profile covers finite tables, projections,
contributions, scalar thresholds and fault evidence, with shrinking and replay.
`StateExecutableFreeze` supplies a computable freeze read proved equal to the
existing semantics; a causal-DAG profile compares roots, cuts, superseded sets
and raw/freeze fault unions against the real Rust fold.
`StateExecutableObservation` connects executable derived/freeze adapters to the
semantic adapters; the events/sum profile exercises separately frozen source
and derived fields against Rust's actual scoped cache.
`StateExecutableContext.read_refinement` connects computable metadata, sealed
rosters, frontiers and complete context fault witnesses to the installed
context reader. Its live profile checks all supported paths, membership queries,
schema markers and combined failures under reordered/duplicate delivery.
Application domains, resources, context freezes and admission remain outside
these profiles. `StateContextCastSyntax` recognizes role/key symbols from raw
binding trees, preserves duplicates for semantic validation and connects the
result to installed context casting with an absent pin. Raw cast oracle cases
cross both S-expression parsers; quoted role/account strings remain distinct
from symbols. Unparseable transport text is an input error; invalid parsed casts
are malformed metadata. The native pin path uses quoted `sha256:` strings with
the strict parser. `StateContextWrapperSyntax` recognizes complete role-wrapper
parameters and exact lowercase-hex64 pins; its installed-cast equation includes
optional pin identity and malformed syntax. The oracle compares parser acceptance
before the independent identity gate, catching native pin grammar bypasses.
`StateContextMessage` derives cast/thread traversal over typed native message
categories, installed profile casting and root decoding. Its outermost cast
wins even when malformed; thread lookup independently reaches the simple
message. The oracle tests strict parsed nesting and generated envelope chains.
General projection from the full native AST, authentication and admission
remain open. BUG-006 remains open for envelopes and suite-qualified keys.

The Batteries gate remains enabled in CI. Intentional constant contribution
arguments and uniform prepared-state receivers have local, explained
`unusedArguments` exceptions. The kernel-generated injectivity lemma for the
large dependent `Prepared` record has a targeted `simpNF` exception because
Batteries exhausts its recursion budget inspecting its type. No module-wide
linter suppression is used.

## Cached checkpoint continuation

`CheckpointAll.render_advance_checkpoint` proves the continuation law for all
16 native state rule heads. `render_advance_wellformed_clause` and
`resolve_fields_complete` connect every well-formed, domain-free native clause
with distinct field names to the existing ordered compiler and evaluator.
Histogram/sum resolve earlier map sources; events use selected ID/signer/value
records. The earlier seven-head `CheckpointKernel` proof remains a dependency and
historical profile, rather than the limit of the new theorem.

```text
render(advance(checkpoint(fields, history), tail))
  = fullFold(fields, history ++ tail)
```

The theorem derives the continuation invariant from genesis and actual updates.
It does not take the desired law as a premise. Snapshot data contains finite
rows, identity membership and projected protocol/resource facts, with no retained
full-history closure. Sets and maps are compared as semantic values; enumeration
order, JSON bytes and serialized checkpoint digests remain separate boundaries.

`CheckpointData` proves compact exists/count/counter/set-union and projected event
invariants. `CheckpointSummary` proves replacement-sensitive live rows and pending
references, including delayed targets and duplicate coverage. `CheckpointCompact`
proves bounded initial ambiguity witnesses and the plain HLC winner. Map rules
retain losing unreplaced candidates because deleting a winner may expose a loser.

`CheckpointEvidence` proves exact projected evidence transport and native
`Repeat.resolve` continuation. `CheckpointAll.position_advance_checkpoint` exposes
that result directly. The Rust repeat cache requires native-admitted, causally
closed histories; the model's arbitrary metadata histories are a broader domain.
Resource facts are transported through the same fixed classifier port on both
sides, as in the existing native kernel model. Native resource extraction,
classification/finalization and cryptography are explicit obligations outside
this theorem; object certificates never create spend authority. The shared Rust
escrow verifier factorization and bounded parity tests provide correspondence
evidence, not a universal Rust extraction proof.

Clock decoding and signer ordering remain fixed typed ports. Domains and global
all-occupant fan-in remain outside the checkpoint implementation profile. Output,
event metadata, protocol facts and resource facts can grow with their respective
state; the theorem makes no constant-storage or resource-verification-time claim.

```sh
lake build LeanCbcl
lake exe runLinter LeanCbcl
lake env lean -t 0 LeanCbcl/CheckpointAllTests.lean
../scripts/check-axioms.sh
python3 ../scripts/check-checkpoint-all16.py
```

See the [checkpoint validation guide](../proofs/cached-checkpoints/README.md)
for recorded acceptance, reproducible trust-zero checks and the exact scope of
bounded Rust/Lean correspondence. Detailed reports are generated locally and
are not checked in.

`StateFaultRendering` proves exact witness membership, uniqueness and UTF-8
byte ordering for canonical fault evidence, then composes executable freeze
witness enumeration with complete fault JSON emission. Equal witness sets yield
identical bytes for a fixed reason and address representation. Recovering
semantic identities from rendered addresses requires injectivity explicitly.
The declarative reference uses merge sort. The live `fault-evidence` profile
executes the operational radix composition proved equal to that reference, and
compares native concurrent-freeze fault strings, including repeated witnesses. Arbitrary UTF-8 aliases operate below admission
and do not establish content-hash identity or resolve root-cast binding.

`StateAddressDigits` refines the radix sorter's key representation: zero is the
missing-byte sentinel, bytes occupy buckets 1–256, and the computed maximum
width makes padded digit comparison exactly equal raw UTF-8 byte comparison.
It also proves that adjacent duplicate removal on sorted output equals finite
set normalization and composes that result with fault JSON emission. The final
result takes permutation and digit ordering as explicit premises; the following
counting/scatter/radix composition derives them in the Nat/function-cell model.

`StateAddressCounting` derives bucket counts, prefix offsets and scatter cursors
from their operational folds and recurrence. It proves destination bounds,
stable placement of equal-key occurrences, disjoint bucket ranges and collision
freedom for distinct occurrence positions. Counts, offsets and partial cursors
fit any word width that represents the input length. Counters are Nat-valued
functions here; the following modules establish scratch permutation and full
least-significant-digit order. Native array/usize extraction remains open.

`StateAddressScatter` executes scratch writes using pre-increment bucket pointers
and derives pointer refinement, retention of every occurrence, destination
coverage and complete pass permutation with multiplicities. It proves ascending
bucket order without supplied permutation or ordering premises and independently
of initial scratch contents. Cells and counters are functions over Nat;
`StateAddressRadix` supplies equal-key secondary stability and full LSD ordering.


`StateAddressRadix` proves secondary-relation stability from operational write
order, equivalence to the reversed-digit fold, complete radix permutation and
lexicographic digit order. It composes native sentinel digit encoding, computed
width, adjacent duplicate removal and JSON emission into exact canonical fault
bytes without caller-supplied sorting or permutation certificates. Initial
scratch contents are unobservable. The oracle now executes this counting/scatter
composition directly, with no reference sorting afterward. Native array/usize
and address-pool representation refinement remain open.


`StateAddressTables` executes counts in a finite Nat array and computes prefix
entries once. It proves full equality with functional initialization, then with
each pass and the complete radix sort. A proved `csimp` substitution selects
this implementation in compiled oracle code; generated C confirms that call.
The byte-key guard recognizes the finite domain, while generic keys and
out-of-table observations retain the original semantics. The live seeded
512-case campaign passes without changing its cases or response deadline.
Finite scratch/word arrays and source-pool extraction are established below;
native control-loop and literal Rust correspondence remain open.

The Rust oracle harness poisons a session before each request and restores it
only after a complete JSON reply. Timeout/disconnection kills the child; later
shrink attempts cannot reuse a late response. An executed regression and two
transport mutations cover that boundary.


`StateAddressArrayScatter` refines complete Nat-array execution of next-pointer
and scratch writes to functional scatter. Bucket membership and allocation
length establish a processed-prefix invariant that derives every destination
bound; out-of-bounds no-op behavior is not used to justify writes. Readback
therefore preserves input multiplicities and composes to the complete radix
semantics for arbitrary initial scratch contents of the required length. The
oracle explicitly calls this proved array implementation; generated C confirms
that call. Word-valued array refinement is established below. Word and source-pool refinement are established below; native control indices
and literal Rust extraction remain separate obligations.


`StateAddressWords` encodes finite Nat arrays into actual `USize` arrays and
proves counter increments and prefix addition commute with that encoding.
Operational input-length bounds establish exact, non-wrapping decoding; byte
conversion plus the sentinel offset is exact on both supported word widths.
Word scratch destination decoding, updates and complete readback refine the
Nat-array execution, including source multiplicities. A checked implementation
preserves the full generic input semantics and composes to the established radix
sort. The oracle explicitly executes `wordSort`, confirmed in generated C.
Source-pool extraction and word-index iteration are refined below. The outer digit-range bridge is established below; literal Rust correspondence
remains open.


`StateAddressPool` models the destructive `Option::take` address move loop.
Radix permutation supplies every index bound and excludes repeated consumption;
checked source lookups prove exact returned values and complete pool clearing.
Duplicate address strings in distinct source slots are preserved until adjacent
deduplication. Concrete finite-pool sorting, moves, deduplication and JSON now
refine canonical fault bytes without an externally supplied total address
callback or pool certificate. The oracle executes that complete path directly.
The word-index/prefix and outer-range bridges are established below; literal
Rust correspondence remains open.


`StateAddressControl` iterates over actual `USize` source indices and writes the
original word index to scratch. It proves byte-bucket conversion, decoded-index
iteration and in-place prefix updates at word positions `1 ≤ k < 257`. Safe
predecessor subtraction and the fixed 257-slot table refine the previous word
prefix semantics. Complete `controlSort` equals the established radix path, and
the source-pool oracle executes it directly, confirmed in generated C. The outer digit-range bridge is established below; literal Rust correspondence
remains open.

The Elephant plan separately requires `lean-ci-green` before `docs-status` can
mark SPEC-038 implemented. CI evidence must identify the tested revision and be
rechecked after relevant pushes; passing local proof gates does not establish CI
success.


`StateAddressRange` executes the outer digit range with a directly recursive
`USize` cursor. The zero guard, exact decrement and decoded decreasing measure
prove termination and the complete descending half-open sequence without supplied
fuel. Native digit-pass execution equals the existing control-sort fold. Width
recognition preserves generic semantics outside the native representable domain,
and the concrete source-pool driver now calls this range implementation,
confirmed in generated C. Literal Rust extraction and the broader kernel
admission/installed-reader ports remain open.
