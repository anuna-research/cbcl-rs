---
id: SPEC-036
title: State kernel denotational correctness and clause composition
version: 0.1.0
status: implemented
last-updated: 2026-11-06
---

# State kernel denotational correctness and clause composition

## Orientation

Intent: prove that complete state clauses compute the declared meaning of their
rules. The named failure is **consistently wrong observations**: order invariance
alone permits an interpreter that always returns zero or silently drops conflicts.
The user authorizes the whole-kernel proof on the existing register-semantics branch.

[[SPEC-019-state-rules]] defines the rules. [[SPEC-035-register-semantics]] adds
explicit host-HLC arbitration. This work composes independent membership,
maximality, finite enumeration and arithmetic specifications into an arbitrary
finite clause theorem, including references to earlier primitive map fields.

Example: a signer register excludes replaced own writes; a histogram counts the
surviving signer groups, not their message count. A separate sum over the same source map adds each
supported group's numeric value once. A domain-excluded replacer changes none of
those observations. Progress reads raw causal evidence rather than the filtered data.

The theorem is about a typed Lean interpreter and its declarative semantics.
Wire parsing, installation recognition, canonical rendering, Rust equivalence,
clock honesty and arbitrary business correctness are separate boundaries.
`bounded-counter` is an explicit delegated resource-verifier boundary: the kernel
adapter must preserve pending/fault tags and derive ready observations from typed
budget evidence. This does not prove the resource verifier's ready/pending/fault
classification or resource-DAG validation. Its separate certification and arithmetic
proofs retain their assumptions; no universal raw-history resource theorem is implied.

Controls: [[SPEC-036-state-kernel-correctness#REQ-3600]] independent semantics;
[[SPEC-036-state-kernel-correctness#REQ-3601]] selections and domains;
[[SPEC-036-state-kernel-correctness#REQ-3602]] reductions and finite maps;
[[SPEC-036-state-kernel-correctness#REQ-3603]] complete rule inventory and composition;
[[SPEC-036-state-kernel-correctness#REQ-3604]] progress/resource boundaries;
[[SPEC-036-state-kernel-correctness#REQ-3605]] falsification and audit.
Next actor: CBCL maintainer reviews the theorem statements, coverage inventory and
recorded independent review. Reviewer path: Orientation, contract, proof boundaries.
Implementer path: grammar, tests, requirements. Paper-author path: theorem and evidence.

## Amendment Channels

The user's task authorizes proof/model/specification changes, not a change to
installed state semantics. Requirements derive from the standing state contracts.
A missing runtime correspondence proof cannot be waived by calling a typed model
an extracted implementation. No amendment presents resource-DAG classification as
proved by an adapter theorem.

## ADR-3600: Independent denotation and verified elaboration

Compose existing selectors and reductions from State.lean with the HLC model and
protocol-position resolver. Specify their outputs independently using logical
membership, greatest elements and arbitrary duplicate-free finite enumerations.
Resolve earlier-field references into typed expressions, then prove evaluation
satisfies those denotations for every successfully elaborated finite clause.

The specification must not invoke executable selections, reductions or the clause
interpreter. Typed field access is an input primitive. Reusing an already proved
component theorem is encouraged; assuming the desired complete observation is not.
Map support is explicit so histograms cannot accidentally count messages instead
of groups. Elaboration coverage connects the fixed surface-rule inventory to the
algebra; quantification over a self-chosen small algebra alone is insufficient.

## Requirements

### REQ-3600: Independent result specifications

Membership, replacement, maxima, cardinality, exact sums and map graph predicates
MUST be defined independently of the executable interpreter. Soundness MUST apply
to arbitrary finite typed inputs satisfying address consistency, not examples only.
Component uniqueness/completeness MUST state the observation equivalence used.
Trace: [[SPEC-036-state-kernel-correctness#TEST-3600]].

### REQ-3601: Domain and selection correctness

Data-domain membership MUST read opener evidence from the raw accepted history.
All applicable domains MUST filter both values and replacement references before
selection. Current selections MUST retain superseded admitted replacement evidence.
Keyed and signer filters MUST preserve missing-field and cross-signer behavior.
Trace: [[SPEC-036-state-kernel-correctness#TEST-3601]].

### REQ-3602: Map and reduction correctness

Greatest-address/HLC choice, existence, cardinality, distinct membership, counter
arithmetic and address-keyed signer/value events MUST meet their independent
specifications. Maps MUST have exact finite support and pointwise specified values.
Histograms MUST count distinct supported keys whose values match; sums MUST add
numeric values once per supported key. Empty and absent values MUST be specified. Map support includes groups whose
chosen payload is absent; event support omits acts with no payload. Histograms
omit absent payloads, and sums project numeric event payloads as well as scalars.
Trace: [[SPEC-036-state-kernel-correctness#TEST-3602]].

### REQ-3603: Surface coverage and clause theorem

Every runtime rule head MUST have an explicit surface constructor or documented
alias normalization, elaboration case and coverage disposition. The proof MUST
cover arbitrary finite clauses with references to earlier compatible map fields.
An independently defined well-formedness predicate MUST imply successful elaboration;
correctness conditional only on successful elaboration is insufficient. Field names
MUST be unique, and outputs MUST preserve every field and its declaration order.
It MUST reject unsupported or forward references rather than silently omit them.
Trace: [[SPEC-036-state-kernel-correctness#TEST-3603]].

### REQ-3604: Extension boundaries

Progress MUST characterize maximum declaratively established protocol positions
using raw accepted addresses. Its proof MUST compose resolver soundness/completeness
rather than treating a claimed rank as trusted. Resource adapter correctness MUST
cover ready arithmetic and pending/fault nonnumeric observations. Classification
and authentication remain explicit verifier/input boundaries, not premises hidden
inside a claimed whole-resource-history theorem.
Trace: [[SPEC-036-state-kernel-correctness#TEST-3604]].

### REQ-3605: Audit and mutations

The general theorems MUST have no sorry or custom axioms. Mutation checks MUST
break covered interpreter behavior and invalidate a corresponding correctness
proof. Independent adversarial and Orientation-only comprehension reviews MUST
record reviewer identities, findings, repairs and remaining boundaries.
Trace: [[SPEC-036-state-kernel-correctness#TEST-3605]].

## CON-3600: Typed surface and interpreter boundary

Input grammar is a finite list of named field entries plus domains. Rule heads
are `last`, `latest-per-signer`, `latest-per-key`, `exists`, `count`, `progress`,
`events`, `set-union`, `values`, `values-per-key`, `register-per-key`, `observed-set`,
`counter`, `histogram`, `sum`, `lww-register`, `lww-per-signer`, `lww-map` and
`bounded-counter`. Multi-value aliases normalize as in
[[SPEC-035-register-semantics#ADR-3502]]. Verb/field operands are typed strings;
optional deletion is Option String. Histogram and sum operands name an earlier
compatible map field. Domains resolve their source to an opener-only list field.

| Surface rule operands | Observation | Coverage disposition |
|---|---|---|
| `last verb value` | optional scalar | greatest address |
| `latest-per-signer verb value` | signer → optional scalar | own-current selection, address choice |
| `latest-per-key verb key value` | key → optional scalar | all matching writes, address choice |
| `exists verb` | boolean | nonempty selection |
| `count verb` | integer | accepted-address cardinality |
| `progress verb` | integer | maximum established position, raw causal evidence |
| `events verb value` | address → signer/value pair | payload-present address groups |
| `set-union verb value` | value membership | all matching writes |
| `values verb value` | value membership | current unkeyed writes |
| `values-per-key verb key value [delete]` | key → value membership | current keyed writes |
| `register-per-key verb key value [delete]` | key → optional scalar | current keyed writes, address choice |
| `observed-set add remove value` | value membership | current writes keyed by value |
| `counter increment decrement amount` | integer | independent exact sums and subtraction |
| `histogram earlier` | scalar → integer count | earlier primitive scalar map, distinct group counts |
| `sum earlier` | integer | earlier primitive numeric/event map, payload sum |
| `lww-register verb value clock` | optional scalar | recognized HLC choice |
| `lww-per-signer verb value clock` | signer → optional scalar | own-current selection, HLC choice |
| `lww-map verb key value clock [delete]` | key → optional scalar | current keyed writes, HLC choice |
| `bounded-counter configuration` | ready/pending/fault tag | delegated typed verifier observation port |

`multi-value-register` normalizes to `values`; `multi-value-map` normalizes to
`values-per-key`. The bounded-counter configuration string is a model port key,
not a proof of the configuration grammar or raw resource history validation.
Histogram and sum references use the six primitive map sources accepted by R7;
histogram excludes events. Neither can reference a histogram, a multi-value map,
or a resource field. Numeric shape checks, required fields, opener uniqueness,
and clock recognition remain installation/input premises outside this typed
elaborator. It is total even on typed acts with missing payloads.

Accepted histories are finite typed acts under NodupAddr. HLC components and
signer-order images are recognized typed evidence at the same boundary as
[[SPEC-035-register-semantics]]. Causal Store/thread/bound inputs use the existing
Repeat model. A resource port supplies a typed verifier outcome, never a caller's
wire-level finalized flag. No new external-input recognizer is introduced.

Pure core: elaboration, domain filtering, selection, reductions, expression and
clause evaluation. Host/verifier boundary: parsing, authentication, resource status
classification, persistence and effects. Output observations are extensional;
JSON byte ordering is outside this theorem.
Implements: [[SPEC-036-state-kernel-correctness#REQ-3600]],
[[SPEC-036-state-kernel-correctness#REQ-3601]],
[[SPEC-036-state-kernel-correctness#REQ-3602]],
[[SPEC-036-state-kernel-correctness#REQ-3603]],
[[SPEC-036-state-kernel-correctness#REQ-3604]].

## Tests

### TEST-3600: Independence and arbitrary inputs (core)

Review denotation definitions transitively for interpreter dependencies. Build
soundness/completeness theorems and audit their assumptions. A constant-zero or
empty-result implementation cannot satisfy the specified nonempty cases.
Validates: [[SPEC-036-state-kernel-correctness#REQ-3600]].

### TEST-3601: Domain and replacement laws (core)

Prove both membership directions for each selection and the raw-opener domain
filter, including multiple domains, excluded replacers and superseded replacers.
Validates: [[SPEC-036-state-kernel-correctness#REQ-3601]].

### TEST-3602: Finite-map laws (core)

Prove exact group support, pointwise choice, event provenance, distinct-value
membership, histogram group cardinality and sum arithmetic. Include missing fields,
empty sources and concurrent candidates. Validates:
[[SPEC-036-state-kernel-correctness#REQ-3602]].

### TEST-3603: Coverage and composition (core)

Exercise every surface constructor and both alias normalizations. Prove the general
elaboration/evaluation theorem; reject a forward or incompatible derived-field
reference. Compare a composed signer-register/histogram/sum example with explicit
expected observations. Validates:
[[SPEC-036-state-kernel-correctness#REQ-3603]].

### TEST-3604: Progress and resource observations (core)

Prove progress equals the maximum established rank, independent of domain filters.
Prove the resource observation adapter preserves pending/fault and computes ready
balances and budgets; retain the verifier classification boundary explicitly.
Validates: [[SPEC-036-state-kernel-correctness#REQ-3604]].

### TEST-3605: Falsification and review (core)

Build Lean, lint, audit axioms and reject deliberate selection/cardinality/map
aggregation/progress mutations through proof failures. Record independent review
and comprehension evidence. Depth: universal Rust/wire/rendering correspondence
and resource-verifier classification proof remain separate maintainer work.
Validates: [[SPEC-036-state-kernel-correctness#REQ-3605]].

## Proof inventory

`StateKernelSemantics.lean` proves independent domain/selection membership and
primitive reduction correctness. `StateKernelQueries.lean` proves choice and
map correctness and extensional completeness. `StateKernelAggregates.lean`
proves histogram cardinalities and exact sums; numeric-cell interpretation has
an independent logical graph. `StateKernelExtensions.lean` connects progress to
`Repeat.At` and specifies the delegated resource adapter.

`StateKernel.lean` proves `evaluate_correct` for every expression constructor.
`StateKernelClause.lean` independently enumerates surface meaning and reference
well-formedness. `compile_clause_complete` proves no supported well-formed clause
is rejected. `whole_kernel_correct` proves any successful clause evaluation meets
that surface meaning. `well_formed_kernel_correct` combines existence and meaning
for every finite well-formed clause and unique-address accepted history. Derived
expressions recompute the referenced source map; component extensional correctness
justifies that observation, without introducing mutable cached state.

These are denotational safety/totality results, not liveness or universal business
refinement. The theorem ranges over arbitrary finite accepted sets, rather than a
particular business example. Existing execution refinement and certification proofs
remain separate compositions with their own premises.

## Implementation and evidence

Plan: [[IMPL-023-state-kernel-correctness]]. Verification and independent review:
[[state-kernel-verification]]. Reproduce with `lake build`, the Lean linter,
`scripts/check-axioms.sh` and `scripts/check-state-kernel.py`. No runtime semantics,
wire grammar, corpus version or installed dialect identity changes in this work.

Open, owner CBCL maintainer: universal Rust/model and rendering correspondence;
resource-verifier classification and resource-DAG compatible-union validation;
proofs connecting host recognition/authentication to the typed input boundary.
