---
id: SPEC-042
title: Boundary Canonicalisation
status: implemented
mode: reference
version: 1.1.0
last-updated: 2026-11-10
owner: CBCL maintainer
---

# Boundary Canonicalisation

| Field | Value |
|---|---|
| ID | SPEC-042 |
| Title | Boundary Canonicalisation |
| Next actor | Implementer: execute the linked plan; independent reviewer: challenge the implementation and evidence |

## Orientation

Authors may write message keywords and sibling dialect shape rules in any order,
including sibling rules nested inside another shape rule. The
library produces a deterministic representation when constructing, serialising,
signing, or addressing those objects. Receipt and folding do not repair objects
or impose declaration-order checks. This amends the rejection approach proposed
on PR 24, following the maintainer's explicit instruction on 2026-11-10.

For example, `:recipient @alice :amount 100` and `:amount 100 :recipient @alice`
have the same message bytes and identity. Keywords sort by their UTF-8 names;
no installed dialect is needed to compute an address. Reordering a positional
argument or an ordinary list remains a meaningful change. Reordering sibling
shape declarations does not change a dialect's signing bytes or self-address.

[[SPEC-042-boundary-canonicalisation#REQ-4206]] requires kernel-checked algorithm
properties, including positional-slot preservation and idempotence.
For recognized unique keyword mappings, equality of complete normal forms is
proved equivalent to equality of positional layouts and complete row mappings.
Recursive shape proofs cover idempotence, structural preservation, and ordering
at every descendant. The checked wrapper computes the input tree's full height
and uses it as the recursion budget; callers do not supply a coverage assumption.
[[SPEC-042-boundary-canonicalisation#REQ-4207]] requires a CI comparison calling
the actual Rust functions against that executable model. The model proof and
the executable conformance check are distinct assurance layers; neither claims
verification of the Rust compiler or its standard library.
The check covers mixed positional slots, opaque values of every Rust atom kind,
prefix/Unicode keys, recursive shape metadata and complete-key tie breakers.

Controls: [[SPEC-042-boundary-canonicalisation#REQ-4201]] prohibits duplicate or
valueless message keywords; [[SPEC-042-boundary-canonicalisation#REQ-4202]]
preserves positional parameter data and values; [[SPEC-042-boundary-canonicalisation#REQ-4204]]
prohibits receipt-time rewriting and order rejection;
[[SPEC-042-boundary-canonicalisation#REQ-4205]] requires explicit identity migration;
[[SPEC-042-boundary-canonicalisation#REQ-4206]] prohibits `sorry`, new axioms and
circular proof premises; [[SPEC-042-boundary-canonicalisation#REQ-4207]] requires
native/model CI conformance and prohibits claiming deductive Rust verification.

Reading paths: maintainers read the decision and migration; implementers traverse
[[SPEC-042-boundary-canonicalisation#CON-4200]] to the test table; reviewers
challenge the controls and boundary coverage. The implementation plan is
[[IMPL-042-boundary-canonicalisation]].

## Failure and intent

The named failure is **map meaning with sequence identity**: two valid spellings
of the same keyword mapping receive different content addresses. Requiring
authors to memorise an ordering moves an implementation obligation into authored
content. The maintainer requests normalisation at both dialect and message
boundaries, with receipt/folding free of repair logic.

## Requirements

### REQ-4200

Message creation, serialisation, signing representation, and addressing SHALL
use the same keyword ordering, independent of dialect installation and author
input order. Applies to simple message parameters and wrapper parameter lists.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4200]].

### REQ-4201

Message recognition SHALL reject duplicate keyword names and missing keyword
values, including lifted `:sender`, `:thread`, and `:caused-by` parameters.
Canonicalisation SHALL NOT collapse duplicate fields or choose a winning value.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4201]].

### REQ-4202

Canonicalisation SHALL preserve positional parameter arguments, their positions
relative to keyword slots in the parameter tail, keyword values, and ordinary
nested data lists. The existing fixed recipient/content slots and lifted header
slots retain their typed message representation, even when source text interleaves
them with keywords. It SHALL NOT
sort arbitrary S-expressions or reinterpret nested keyword-looking data as maps.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4202]].

### REQ-4203

Dialect creation and signing/addressing SHALL canonically order sibling shape
rules recursively and independent shape declarations. Positional extend
parameters, templates, inheritance order, and state field dependency order SHALL
remain ordered. Signature verification SHALL reconstruct the same representation.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4203]].

### REQ-4204

Receipt and state folding SHALL neither rewrite messages nor reject otherwise
valid messages because of keyword order. Checkpoint coordination SHALL enforce
the exact field set and uniqueness without requiring a field order.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4204]].

### REQ-4205

Canonical signing-form and typed-address versions SHALL advance. Affected
fixtures SHALL be regenerated explicitly. Existing affected signed objects and
causal references require reissue; implementations SHALL NOT retry an older
ordering when signature verification fails.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4205]].

### REQ-4206

The canonicalisation algorithm SHALL have kernel-checked proofs of idempotence,
canonical ordering, preservation of complete keyword/value pairs and positional
slots, and permutation independence for unique keyword mappings with identical
positional layouts. Recursive dialect sibling normalisation SHALL have a
kernel-checked fixed-point and preservation argument. Proofs SHALL NOT use
`sorry`, new axioms, or a premise asserting the property being proved.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4206]].

### REQ-4207

CI SHALL compare the actual Rust canonicalisation functions directly against the
executable formal model, including mixed positional slots, opaque nested values,
prefix and Unicode keys, and recursive shapes. The conformance check SHALL fail
under deliberate mutations of sorting and slot/value preservation. This check is
executable conformance evidence; it SHALL NOT be described as a deductive proof
of the Rust compiler, standard library sort, or complete Rust implementation.
Trace: [[SPEC-042-boundary-canonicalisation#TEST-4207]].

## ADR-4200

Use lexical keyword ordering in the shared core boundary representation. Reuse
the existing typed message parser, serializer, dialect signing form, and Merkle
field encoder from [[SPEC-017-typed-content-addresses]]. Do not alter the generic
S-expression encoder, whose injectivity is an existing contract. This is the
minimum new code in existing components; no registry-dependent hash API or
receipt normaliser is needed. Shape conjunctions are unordered declarations;
template parameters and state field dependencies are sequences.

## CON-4200

Input grammar is the existing typed message grammar in [[SPEC-001]] and shape
grammar in [[SPEC-002-structural-contracts]]. In a parameter list, recognition
consumes either a positional expression or `keyword value`; a keyword without a
value and a repeated keyword are errors. Sort whole keyword/value pairs by
keyword name, replacing only keyword/value slots. Do not descend into values.
The fixed recipient/content slots and lifted header fields retain the serializer's existing fixed positions.
Wrappers recurse only into the recognized inner message.

Dialect shape rules recursively sort by keyword name, with max-depth rules
after keyword rules and canonical encoded bytes as a deterministic tie breaker.
Shape declarations sort by performative name, then canonical encoded bytes.
Creation normalises the typed dialect after compiler-inserted fields; signing
and hashing reconstruct that same shape representation for directly built dialects.

## Acceptance tests

All cases are runnable core acceptance. Existing parser, binding, state vector,
and checkpoint suites supply integration coverage.

| Test | Requirement | Evidence |
|---|---|---|
| TEST-4200 | [[SPEC-042-boundary-canonicalisation#REQ-4200]] | Permuted simple and wrapped messages yield equal serialisation, roots, openings and signing preimages; direct typed construction agrees |
| TEST-4201 | [[SPEC-042-boundary-canonicalisation#REQ-4201]] | Duplicate ordinary/lifted/wrapper keywords and missing values fail recognition |
| TEST-4202 | [[SPEC-042-boundary-canonicalisation#REQ-4202]] | Reordered positional data and nested lists retain distinct bytes and roots; normalisation is idempotent |
| TEST-4203 | [[SPEC-042-boundary-canonicalisation#REQ-4203]] | Permuted nested shapes produce equal dialect identities and valid cross-order signatures; changed constraints invalidate signatures |
| TEST-4204 | [[SPEC-042-boundary-canonicalisation#REQ-4204]] | R7 accepts both field orders without mutating typed messages; checkpoint corpus still passes |
| TEST-4205 | [[SPEC-042-boundary-canonicalisation#REQ-4205]] | Version assertions and regenerated fixture comparisons pass; deliberate mutation of ordering makes acceptance fail |
| TEST-4206 | [[SPEC-042-boundary-canonicalisation#REQ-4206]] | Build canonicalisation theorem module and audit all its proof dependencies |
| TEST-4207 | [[SPEC-042-boundary-canonicalisation#REQ-4207]] | Direct Rust/formal-model conformance campaign and deliberate mutations |

## Migration and enable path

This is a protocol/library change, enabled by adopting this version together at
authoring and verification boundaries. There is no runtime fallback or hidden
repair switch. Maintainers must tell downstream signers and stores to reissue
affected dialects, signatures, acts, and descendant causal references before
adoption. Rollback restores the previous library and its matching data set;
mixing old and new addresses within a history is unsupported. Unaffected objects
retain their bytes. PR 31's audience extraction remains independent of ordering.

## Amendment Channels

The CBCL maintainer may amend this specification through repository changes or
explicit task instructions. No channel may waive duplicate rejection, preservation
of positional values, or signature verification without a replacement contract
and corresponding acceptance tests.

## Verification status

Implemented on `feat/canonical-boundaries`, based on main revision
`0eaf685dc815d181c5a5e3fed12265de1227a906`. This document does not claim a Lean
refinement proof for the concrete canonical encoding.

The implementation started with observed failing boundary tests: keyword and
wrapper permutations, duplicate recognition, shape creation, and version checks.
The positional-data case already passed and remains a preservation check.
After implementation the focused suite passes. Deliberately removing parameter
sorting, disabling shape normalisation, and permitting duplicate keywords each
made its corresponding executed regression test fail. Sources were restored
after each mutation.

| Command | Observed result |
|---|---|
| `cargo test -p cbcl-core -p cbcl-parser -p cbcl-wasm -p cbcl-erl --no-fail-fast` | Core, parser, WASM, Erlang and conformance suites pass; the corpus target was rerun after the final manifest edit |
| `cargo test -p cbcl-parser --test state_corpus` | Forward, reversed, duplicate and archived migration checks pass with the final manifest |
| `cargo test -p cbcl-parser --test boundary_canonicalisation` | Boundary acceptance passes, including direct construction and nonmutating R7 receipt |
| `cargo check -p cbcl-core -p cbcl-parser --no-default-features` | Pass |
| `cargo check -p cbcl-wasm --target wasm32-unknown-unknown` | Pass; existing mutable-static warnings remain |
| `cargo test -p cbcl-checkpoint --lib` | Same failing test-name set as an independent run on untouched main: progress-derived-act and recipient-alias defects; no additional failures |
| `zetl check --dead-links --fail-on error` and `zetl check --fail-on error` | Fail on the pre-existing dead-link set; comparison with untouched main finds no new dead links or syntax errors |
| `git diff --check` | Pass |

Builds used external storage with `CARGO_INCREMENTAL=0`,
`CARGO_PROFILE_DEV_DEBUG=0`, and `CARGO_PROFILE_TEST_DEBUG=0` after the original
volume ran out of space. Checkpoint tests used an external `TMPDIR` as well.

Independent reviewer session `canonical_review` inspected the specification and
deliverable and reproduced the baseline checkpoint failures. Its findings were
wrapper suffix tokens being discarded and an overbroad positional-slot promise.
Recognition now rejects suffix tokens; the contract explicitly distinguishes
fixed content/header slots from positional parameter slots. Re-review found no
remaining concrete defect. Fresh-context session `canonical_orientation` passed
the comprehension gate after nested sibling rules were made explicit.

The existing multihash migration and historical archive remain unchanged. The
new `state-boundary-canonicalisation-migration.json` records historical `old`,
immediately preceding `previous`, and current `new` addresses. Every `previous`
address was compared against the corresponding main fixture. Admission verdicts
are unchanged. The signer-supersession and tags-and-balance rendered states only
change their address-keyed entries; application values remain unchanged.

Next actor: maintainer reviews the branch and coordinates reissue with downstream
signers and stores before adoption. The existing checkpoint baseline defects
remain maintainer-owned follow-up work, outside this boundary rule.

### Oracle parity follow-up

Lean's keyword-extraction campaign previously modelled only R7's duplicate
nonrouting-key gate. Its wrapper called native message recognition on the Rust
side, so repeated `:thread` keys disagreed after boundary rejection was introduced.
Its shape scan also used authored row order, disagreeing on keyword-looking
values after Rust canonicalised the message. These are boundary-model gaps,
not reasons to relax [[SPEC-042-boundary-canonicalisation#REQ-4201]].

The oracle now applies complete keyword-row recognition and all-key uniqueness,
then canonicalises whole rows before shape checks and extraction. Lower-level
R7 extraction and its existing proofs are unchanged. New Lean lemmas establish
boundary recognition soundness and preservation of the row multiset by sorting;
their scope is the keyword-only profile, not the full native message grammar.
Routing-duplicate and order-sensitive literal regressions run natively without
Lean and against the live oracle. Independent session `keyword_oracle_review`
found no concrete defects in this follow-up.

Validation: `lake build cbcl-state-oracle LeanCbcl.StateKeywordExtractionTests`
passes. `cargo test -p cbcl-parser --test state_kernel_oracle -- --include-ignored`
passes all executed campaigns. The original failing routing-duplicate case was
observed red against the previous oracle before the fix. An axiom audit of the
new boundary lemmas, their fixtures, and the existing checked-amount theorem
finds only `propext`, `Classical.choice`, and `Quot.sound`.

### Formal canonicalisation assurance

The failure addressed by [[SPEC-042-boundary-canonicalisation#REQ-4206]] is that
example permutations and a row-sorting lemma leave the complete transformation
unchecked: collection can split a key from its value, replacement can move a
positional argument, and recursive shape normalisation can stop before a child.
The maintainer requested a formalised check of the canonicalisation function.

`BoundaryCanonical` models the actual collect/sort/replace algorithm over opaque
values, followed by its scanner/flat-token representation. Its kernel-checked
contracts include:

| Theorem | Property |
|---|---|
| `canonical_layout` | Every positional value and pair-slot position is retained |
| `canonical_fields`, `canonical_preserves` | Exactly the original complete rows are emitted, in prescribed UTF-8 key order, with multiplicity retained |
| `canonical_idempotent`, `tokens_idempotent` | Reapplying the complete transformation changes nothing |
| `canonical_permutation`, `tokens_permutation` | Unique keyword mappings with the same positional layout have one normal form |
| `canonical_eq_iff`, `tokens_eq_iff` | Equal complete normal forms are equivalent to equal positional layouts and complete row mappings; different values cannot be collapsed |
| `scan_flatten` | Recognized pair/positional structure is reconstructed without treating keyword-looking values as keys |

The flat-token results require the explicit recognizer/keyword-constructor law
and a recognized positional layout. The concrete JSON adapter proves its
keyword-constructor law. Duplicate rejection remains the recognition contract;
the row sorter does not discard or merge duplicates.

`BoundaryShapeCanonical` proves recursive structural preservation modulo sibling
permutations, exact height preservation, and complete ordering/idempotence for
the wrapper that computes its own tree-height budget. The comparator's complete
native key remains a conformance boundary: generic tree properties do not prove
the native shape encoder injective or independently prove shape permutation
independence under that encoding.

The `canonicalisation` oracle profile executes these exact definitions. The
native campaign calls `canonical_params` and `canonicalise_dialect` directly;
no message parser or receipt substitutes for either function. Parameter cases
include every permutation/positional layout of a fixed unique-row example and
generated mixed slots, all native atom kinds as opaque values, duplicates,
dangling keys, nested data, prefixes and arbitrary Unicode keys. Shape cases
include recursive require/optional children, distinct same-name declarations,
constructor/type/default/max-depth/descendant tie breakers and deep metadata.
The adapter independently computes byte-length framing and complete subtree
keys from transported typed atom octets. Shape transport rejects trees beyond
its explicit depth budget of 16 and metadata beyond 32; encoding accepted trees
is structural and never truncates or silently substitutes empty keys.

CI builds the proof modules through `LeanCbcl`, audits every named theorem in
the existing axiom allowlist gate, and runs the native/model campaigns in the
mandatory state-oracle suite. It also runs the reproducible
`scripts/check-boundary-canonicalisation-mutations.py`: removing pair sorting,
changing opaque values, changing positional slots, skipping recursive child
normalisation, and skipping top-level shape sorting must each fail an executed
conformance test. Sources are restored and clean-code conformance is required
afterward; compile and recognized oracle-infrastructure failures do not count
as mutation kills.

The verified model has unbounded algorithm theorems. The native atom-octet map,
typed-AST transport, concrete native comparator/key construction, compiler and
standard-library implementation are tested boundaries, not deductively verified
Rust. This distinction is part of the acceptance contract, not a deferred proof
silently treated as complete.

Acceptance evidence: `lake build cbcl-state-oracle LeanCbcl` passes; the existing
`scripts/check-axioms.sh` gate passes with all new theorem entries included.
The new theorem dependency set contains only `propext`, `Classical.choice`, and
`Quot.sound`. Batteries lint passes separately for `BoundaryCanonical`,
`BoundaryShapeCanonical`, and `BoundaryCanonicalOracle`. The complete
state-kernel oracle suite and boundary regressions pass with the CI seed and
case configuration. The reproducible mutation script rejects every listed
mutant and passes the restored implementation. No production representation
changes are introduced by this assurance extension.

Independent session `canonical_formal_review` challenged the model, theorem
premises, computed-depth wrapper, transport and CI. Findings about truncated
metadata, depth coverage, audit inventory, workflow triggers and deterministic
tie-break cases were resolved. Final re-review found no concrete blocker.
Fresh-context session `canonical_orientation` confirmed the distinction between
proved generic properties and tested native correspondence; the Orientation
explicitly identifies the wrapper that supplies complete depth coverage.
