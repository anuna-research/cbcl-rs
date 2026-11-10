---
id: SPEC-042
title: Boundary Canonicalisation
status: implemented
mode: reference
version: 1.0.0
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

Controls: [[SPEC-042-boundary-canonicalisation#REQ-4201]] prohibits duplicate or
valueless message keywords; [[SPEC-042-boundary-canonicalisation#REQ-4202]]
preserves positional parameter data and values; [[SPEC-042-boundary-canonicalisation#REQ-4204]]
prohibits receipt-time rewriting and order rejection;
[[SPEC-042-boundary-canonicalisation#REQ-4205]] requires explicit identity migration.

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
