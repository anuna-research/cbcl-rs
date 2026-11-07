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
