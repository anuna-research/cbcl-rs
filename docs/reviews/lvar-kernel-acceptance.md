---
title: LVar kernel acceptance evidence
mode: reference
---

# LVar kernel acceptance evidence

The implementation is **not complete**. This matrix records the v0.3 acceptance
checkpoint: typed agreement for the prior single-source inventory is complete.
The maintainer has since approved v0.4 sealed-wrapper migration and authored
product conditions. Native root migration and native condition execution are
implemented; extended compiler/oracle proofs and full TEST-3815 acceptance
remain pending. The older rows below are evidence for the checkpoint,
not completed acceptance of the expanded v0.4 inventory. This audit concerns [[SPEC-038-lvar-state-kernel]] and the
execution plan [[IMPL-030-lvar-state-kernel]]. Completing the audit does not
complete either specification or plan.

The audited v0.3 runtime/proof revision is `63b8431`; the rows below retain that
checkpoint's scope. Subsequent work preserves the original historical-byte
snapshot and implements the approved v0.4 sealed-root migration. Its separate
verification record follows; authored conjunction proof/oracle integration
remains outstanding.

## Sealed-root migration verification

Construction and cached identity validation hash exactly the selected outermost
sealed wrapper for causal role roots. Public candidate admission now rejects
stale cached identities before appending a candidate. Root discovery and progress
share the transparent-wrapper traversal, and progress pins the actual state root
address. The discovered failures are [[BUG-017-native-admission-trusts-cached-act-identity]]
and [[BUG-018-state-root-discovery-stops-at-transport-wrapper]].

`test-vectors/state-role-root-migration.json` declares every old/new message
address for bounded-ceiling, bounded-coin and checklist-roles. The original
`state-pre-lvar-bytes.json` remains unchanged. The corpus compares the full
reissued vectors to typed reference-only transformations, including sorted
address sets, verdict keys and bound intent results; every original literal
state byte remains checked. Unaffected histories retain original addresses.
See the [migration procedure](../reference/state-language.md#root-addresses-and-migration).

Local verification after the migration: core library 881 and parser library 164
pass; native integration suites pass (context 19, admission 5, corpus 2,
exports 2, state layer 12, resource 15, finite 13, freeze 20, factorisation 4,
progress 11, thresholds 15). The live Lean oracle passes all 15 suites with
seed 380038/cases 512, plus the separate kernel-reduced Lean progress comparison.
The pinned-source baseline generator reproduces all eight original snapshots.
Independent semantic review found no concrete defect in the migration or its
root-discovery/progress integration. The final isolated mutation gate rejects six executed mutants: cast omission,
wrong root predicate, skipped candidate validation, transport-stopping discovery,
legacy progress pinning and raw-render whitespace drift. An earlier disk-space
failure was discarded as infrastructure failure; no compiler failure counts as
mutation rejection.

Remote required Lean build/audit and parity jobs succeeded for contract commit
`1aac6ee` (run 321). That run predates the runtime migration and does not verify
these runtime changes or the outstanding authored conditions.

## Authored condition implementation checkpoint

The native `Condition` tree recognizes exact `read` forms and nested `and` forms
with at least two children. Installation reuses existing singleton source checks
for every leaf, preserves earlier-source ordering and clause-wide freeze
eligibility, and checks expression size/scalar bounds and rendered-field limits.
Evaluation collects every fault before normal success and uses each leaf's own
source scope. Conditions render Boolean true on success; direct thresholds retain
their authored alternative. Canonical hashing, schema output, description output
and the EBNF include the new form.

The threshold suite passes 21 tests, including six new authored-condition cases.
The complete committed parser inventory passes 491 tests. Five native semantic
mutants are rejected: pending short-circuit, overwritten evidence, shared freezer
scope, unary recognition and skipped condition-size checking. Independent review
found no concrete native defect. The previous 15 live Lean oracle suites still
pass (seed 380038/cases 512); those suites do **not** yet exercise authored
conditions.

`StateCondition` supplies reviewed Boolean/fault algebra lemmas. Its module lint
passes, and three proof mutants are rejected by the pending/fault, evidence-union
and successful-Boolean theorems. This module does not establish installed leaf
query or scope correspondence. Extending the actual authored compiler, live
oracle, witness replay, convergence and full agreement capstone remains required
by [[SPEC-038-lvar-state-kernel#TEST-3815]]. No v0.4 completion is inferred from the
prior single-source capstone or this algebra checkpoint.

`StateConditionCompiler` now binds each leaf to an actual completed source plan
and singleton query, dispatches it with that source's `referenceScope`, and proves
whole-tree refinement to independent installed-policy interpretation. It rejects
empty/unary conjunctions and excess node budgets. Independent proof review found
no concrete defect; three additional proof mutants reject full-history scope
substitution, discarded fixed bounds and skipped compiler size checks. Full Lean
build and Batteries environment lint pass; the axiom audit reports 2381 theorems,
all allowlisted. Earlier-source eligibility and alignment between prepared
source plans/definitions still need to be derived through the actual authored
walk, then the emitted observation proofs and oracle must be extended.

## Requirement evidence

“Tested” records executed native checks, not a universal Rust source-extraction
proof. “Proved” refers to the typed Lean model with its explicit structural
premises. A green test does not resolve a conflicting contract.

| Requirement | Checkpoint evidence | v0.3 acceptance state |
|---|---|---|
| [[SPEC-038-lvar-state-kernel#REQ-3800]] | `StateLift`, concrete installed factories and authored source lowering; `lattice_factorisation` checks forward/reverse/duplicate display and partition union, including conflicting domain initializers. `progress` and resources use history terms. | Proved and tested for the closed inventory. Product-read extension is separately incomplete below. |
| [[SPEC-038-lvar-state-kernel#REQ-3801]] | Shared lattice contribution/join path in `lattice.rs`; generic lift/set-union theorems and factorisation suite. Duplicate delivery is also exercised by native thresholds, context and the live oracle. | Proved and tested. |
| [[SPEC-038-lvar-state-kernel#REQ-3802]] | `threshold_reads`; checked finite policies; authored data, membership, event-sum, progress and finite preservation modules. `StateAuthoredThresholdOrigin.quasi_determinism` derives original source policy and actual output success, covering every source rule. | Proved and tested for recognized single-source thresholds. Compound authored syntax is not supplied by this result. |
| [[SPEC-038-lvar-state-kernel#REQ-3803]] | `freeze_reads` tests both policies, concurrent/late writes, nested independent cuts, raw/domain/context/resource evidence and witness-only recompilation. `StateAuthoredFrozenAgreement` proves actual emitted same-freezer payload agreement with differing exclusions. | Proved and tested. |
| [[SPEC-038-lvar-state-kernel#REQ-3804]] | Core initializer/resource/freeze faults and dependent propagation; missing-resource-reference regression; finite/domain/freeze witness replay tests. `StateEvidenceSupport`, concrete replay certificates, and actual authored output replay establish finite accepted evidence and containing faults. | Proved and tested. |
| [[SPEC-038-lvar-state-kernel#REQ-3805]] | `state_schema` and `state_exports`, threshold/freeze/context schema checks; snapshot-effect warnings in JS, WASM, C and Erlang READMEs. Immutable context paths are marked separately from changing observations. | Tested; required host documentation present. |
| [[SPEC-038-lvar-state-kernel#REQ-3806]] | `StateAuthoredQuasiDeterminism.authored_quasi_determinism` aggregates actual output threshold/frozen agreement, exact equal-set vectors, immediate accepted-witness replay, finite witness dissemination, finite-history convergence and no-top complete-data SEC. Ongoing threshold preservation remains in the concrete preservation modules. | Typed model proved; full build/lint/axiom gates, semantic mutations and independent review pass. Native identity/extraction assumptions remain explicit. |
| [[SPEC-038-lvar-state-kernel#REQ-3807]] | `state_corpus` checks current vectors against their expectations, and all eight original pre-SPEC vectors against literal historical render bytes, addresses, verdicts and applicable intents; current implementation preserves wire identity. [[BUG-011-root-address-does-not-commit-sealed-cast]] records the conflict with wrapper commitment required by [[SPEC-014-role-layer-endpoint-projection#REQ-625]]. | Existing vectors tested at v0.3. Migration is now authorized; implementation and explicit mapping evidence are pending. |
| [[SPEC-038-lvar-state-kernel#REQ-3808]] | History-backed `progress`/`bounded-counter` terms retain their specialized algorithms. Progress native/Lean comparison and resource oracle profiles run; concrete resource cone/frontier/budget, aggregate/solvency and verifier-certificate equivalence proofs remain composed. | Proved and tested for supported profiles; unsupported collective profiles retain their documented fault behavior. |
| [[SPEC-038-lvar-state-kernel#REQ-3809]] | Internal pair lattices, dependent sum/histogram, native scoped composition and their proofs exist. The closed authored menu lacks conjunction/comparison syntax and semantics promised by this requirement. [[BUG-012-product-read-composition-has-no-authored-contract]] contains a concrete proposal. | **Incomplete; authored contract approved, implementation pending.** Internal products do not satisfy the missing authored operation. |
| [[SPEC-038-lvar-state-kernel#REQ-3810]] | `finite_lattices`, concrete finite-table/contribution/projection validation, actual finite-query preservation, dense/upper-cache refinement, live finite oracle and cubic validation counter test. | Proved and tested. |
| [[SPEC-038-lvar-state-kernel#REQ-3811]] | `state_context` and live context oracle cover typed paths, role rosters, metadata, malformed/conflicting evidence, pins, markers and receipt order. Whole context changes remain snapshots; no quorum policy is introduced. | Data access tested and typed model proved. Native wrapper commitment remains unimplemented under [[BUG-011-root-address-does-not-commit-sealed-cast]]. |
| [[SPEC-038-lvar-state-kernel#NFR-3800]] | Documented `O(t n log(n+1))` ordinary work and `O(t(d+1)n log(n+1)+tnf)` frozen work; complete concurrent witnesses may be quadratic. Validators retain separate bounds. Exact pair-count and `n³` associativity-count tests pass; upper-set preprocessing is separated from pair checks. | Source operation bounds and counter tests checked. No end-to-end linear or wall-clock claim, and no mechanized runtime-complexity theorem claimed. |

## Contracts and tests

| Contract | Recognition and semantics | Remaining limitation |
|---|---|---|
| [[SPEC-038-lvar-state-kernel#CON-3800]] | Closed Rust lattice/term/post inventory and Lean installed-rule algebra; factorisation and composition proofs. | Its product post-map menu must be reconciled with the authored requirement in [[BUG-012-product-read-composition-has-no-authored-contract]]. |
| [[SPEC-038-lvar-state-kernel#CON-3801]] | Parser and install checks for source-relative threshold alternatives, incompatibility, types, nonnegative sums and fault rejection. | Compound product reads have no complete authored contract. |
| [[SPEC-038-lvar-state-kernel#CON-3802]] | Recognized source/verb/policy form; installation and role admission; exact earliest causal cut and attributable concurrency evidence. | No unapproved contract change. |
| [[SPEC-038-lvar-state-kernel#CON-3803]] | Finite table/contribution/projection grammar, bounded size and verified algebra/stable projection rules. | No caller code execution or unverified projection accepted. |
| [[SPEC-038-lvar-state-kernel#CON-3804]] | Closed typed context paths and generic read-only data, roster domains and membership reads. | Native root identity decision remains open; no invented quorum primitive. |

The decision record remains unchanged: [[SPEC-038-lvar-state-kernel#ADR-3800]]
selects LVars; [[SPEC-038-lvar-state-kernel#ADR-3801]] admits verified data tables
rather than arbitrary code; [[SPEC-038-lvar-state-kernel#ADR-3802]] specifies
concurrent freezes; [[SPEC-038-lvar-state-kernel#ADR-3803]] requires sticky top;
[[SPEC-038-lvar-state-kernel#ADR-3804]] treats shipped heads as abbreviations;
[[SPEC-038-lvar-state-kernel#ADR-3805]] distinguishes stable thresholds and
revisable snapshots; [[SPEC-038-lvar-state-kernel#ADR-3806]] retains history
terms for closure algorithms. No LVish implementation code was copied or
translated by this work.

| Test | Executed or inspected evidence |
|---|---|
| [[SPEC-038-lvar-state-kernel#TEST-3800]] | `lattice_factorisation`, core lattice laws, distinct-initializer regression and history-backed closure paths. |
| [[SPEC-038-lvar-state-kernel#TEST-3801]] | `threshold_reads`, finite alternatives, native progress comparison and live oracle permutations/duplication. |
| [[SPEC-038-lvar-state-kernel#TEST-3802]] | `freeze_reads` and live causal-DAG/nested/resource freeze profiles. |
| [[SPEC-038-lvar-state-kernel#TEST-3803]] | Compatible/duplicate/mistyped/fault alternative rejection; signed sum rejection, negative-shape recognition and exact pair-comparison count. |
| [[SPEC-038-lvar-state-kernel#TEST-3804]] | Core faults, contextual/domain/resource composition, witness-only replay and live fault/evidence profiles. |
| [[SPEC-038-lvar-state-kernel#TEST-3805]] | `state_exports`, schema cases and binding README warnings. |
| [[SPEC-038-lvar-state-kernel#TEST-3806]] | Whole typed capstone, `lake build`, Batteries env-linter, axiom audit, semantic mutants and independent review. |
| [[SPEC-038-lvar-state-kernel#TEST-3807]] | `state_corpus` plus the pinned pre-SPEC raw-byte baseline on all original inputs. These do not select a root identity migration. |
| [[SPEC-038-lvar-state-kernel#TEST-3808]] | `finite_lattices`, core `verification_visits_exactly_n_cubed_associativity_triples`, live finite/numeric/Boolean profiles and validators. |
| [[SPEC-038-lvar-state-kernel#TEST-3809]] | `state_context`, context role/metadata/fault oracle and native context freeze/domain tests. Hash correctness, signatures and protocol admission are explicit profile boundaries. |

## Reproduction and current results

Run Lean commands from `lean-cbcl/`. Rust test runs use
`CARGO_INCREMENTAL=0 CARGO_PROFILE_TEST_DEBUG=0`.

```sh
lake build
lake exe runLinter LeanCbcl
bash ../scripts/check-axioms.sh
```

At `63b8431`, build and Batteries lint pass. The axiom audit reports
`OK: 2359 theorem(s) audited; all axioms allowlisted.` No new `sorry` or custom
axiom is introduced. The direct witness and frozen output proofs received
independent read-only review before completion was recorded in Elephant.

```sh
python3 scripts/check-state-lvar-mutations.py \
  --module StateLVar --module StateFrozenSuccess \
  --module StateDataLocalWorld --module StateAuthoredFrozenAgreement
```

All selected mutations are rejected: dependency top, raw history, initializer
top, ignored causal cut, omitted freezer, omitted witness address, mismatched
freezer identity, erased normalization and mismatched output name.

```sh
cargo test -p cbcl-core -p cbcl-parser --lib
cargo test -p cbcl-parser \
  --test admission_state_free --test finite_lattices --test freeze_reads \
  --test lattice_factorisation --test state_context --test state_corpus \
  --test state_exports --test state_layer --test state_progress --test threshold_reads
PROPTEST_RNG_SEED=380038 PROPTEST_CASES=512 \
  cargo test -p cbcl-parser --test state_kernel_oracle -- --ignored
cargo test -p cbcl-parser --test state_progress \
  native_progress_matches_kernel_reduced_lean -- --ignored
cargo test -p cbcl-parser --test state_kernel_oracle
```

Fresh audit runs pass the core library (881 tests), parser library (164 tests),
and the selected parser suites. Their individual results are: admission 5,
finite lattices 13, freeze 20, factorisation 4, context 15, corpus 1, exports 2,
state layer 12, progress 11 and thresholds 15. The later byte-baseline addition increases
`state_corpus` to 2 passing tests (current corpus plus pinned historical corpus). The normal progress invocation
leaves its separately invoked Lean comparison ignored; it is not silently
counted as executed. The live oracle passes its ignored profiles with seed
`380038` and 512 generated cases per configured property, including role rosters,
metadata projections and fault evidence. These bounded profiles do not establish
universal native parser/authentication/renderer extraction.

The separately invoked native/Lean progress comparison passes (1 test). The
ordinary oracle transport-failure unit also passes (1 test; the 15 ignored
profiles were run separately). The live oracle result is
`15 passed; 0 failed; 0 ignored; 1 filtered out`; that filtered nonignored unit is
covered by the final command.

## Historical byte compatibility

Review found that the former corpus baseline parsed rendered state as JSON.
That checked semantic values but could hide formatting or numeric changes.
The strengthened `pre_lvar_vectors_preserve_exact_render_bytes` test consumes
`test-vectors/state-pre-lvar-bytes.json`. Its pinned pre-SPEC revision is
`3e222b072070eb1b4052fb5d448e899aa65967f3`, where SPEC-038 does not yet exist.
Commit `f8a7098` adds the fixture and its regression/reproduction checks. The
fixture retains every original input vector and literal render string.
Current addresses, verdicts, applicable intents and raw rendered bytes pass for
all eight original state-corpus vectors without compatibility exemptions.
This is the original state corpus, not every vector elsewhere in the repository.

```sh
python3 scripts/generate-state-byte-baseline.py --check
cargo test -p cbcl-parser --test state_corpus
python3 scripts/check-state-oracle-mutations.py \
  --mutant pre-spec-render-bytes-add-whitespace
```

The generator extracts the original revision into a temporary checkout and
inserts only a raw-capture print into its historical corpus test. The historical
suite must pass before a fixture can be generated. `--check` reproduces the
committed fixture exactly. A pinned filename manifest prevents omitted original
vectors; retaining original inputs prevents edited modern cases from hiding a
break. The isolated mutation adds only JSON whitespace to the actual native
renderer; the executed raw-byte assertion rejects it. Historical checks also
pass under `STATE_CORPUS_WRITE=1`, leaving fixture bytes unchanged, while normal
vector authoring remains available.

## Author documentation and remaining work

README links dialect authors to `docs/cbcl-grammar.ebnf` and
`docs/reference/state-language.md`; the reference gives keywords, argument
forms, installation rejection rules and observation semantics. The JS, WASM, C
and Erlang READMEs explain snapshot effects and threshold/frozen finality. The
Lean README and concept guide distinguish typed-model proofs from their native
input boundaries. The approval-count example explicitly counts distinct acts;
it does not claim a distinct-reviewer `signers` primitive exists.

Required remaining implementation work follows the approved decisions recorded in
[[BUG-011-root-address-does-not-commit-sealed-cast]] and
[[BUG-012-product-read-composition-has-no-authored-contract]]. The review-only
identity patch is not an applied implementation. Product read composition is not
waived or replaced by a finite-lattice workaround. Implement the chosen forms, refresh grammar/docs/tests and rerun affected gates.
Only then can the v0.4 audit and final documentation/status acceptance close.

Latest-SHA CI is a separate gate. At this audit checkpoint the required run for
`c781617` passed; after pushing `63b8431`, required Lean run 319 and mutation run
320 are pending, while its parity job passed. The newer local byte-acceptance
commit `f8a7098` has not yet been pushed and has no CI result. A previous green
revision is not latest-revision acceptance.
No failed required check is hidden with `continue-on-error`; the optional
Forgejo Lean cache was removed after it prevented bootstrap from starting.

At the proof checkpoint, the specs-only link check reports links to the
existing BUG-011/BUG-012 files outside its sub-vault; the whole-root comparison
adds no unresolved source-target pairs. Adding this audit introduces whole-root
warnings for its references to the existing SPEC-014/SPEC-038 files in the
nested specs vault. The referenced files exist. Existing cross-vault link debt
remains visible; this audit does not claim a globally clean link graph.
