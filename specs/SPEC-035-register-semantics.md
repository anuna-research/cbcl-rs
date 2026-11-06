---
id: SPEC-035
title: Explicit LWW registers and opener-only initialization
version: 1.0.0
status: implemented
last-updated: 2026-11-06
---

# Explicit LWW registers and opener-only initialization

## Orientation

Intent: expose one clock-ordered register family and conflict-preserving alternatives.
The user rejects content-address arbitration as the primary register policy and
has explicitly confirmed content address only as an exact HLC/signer tie-break.
The current register/initializer heads are `lww-register`, `lww-per-signer`, `lww-map`, and `initial`.
`initial` reads the sole distinct raw opener; it never arbitrates between writers.
Missing or several opener candidates yield Absent, before projecting the field.
Repeated receipt of one opener preserves its value. Conflict-preserving forms are
`multi-value-register` and `multi-value-map` (aliases of `values` and `values-per-key`).
LWW selects the greatest tuple of HLC, authenticated signer, then content address. LWW clocks have declared shape type `hlc`, with a canonical string wire value.
Hosts generate, advance and persist honest clock evidence; clock shape does not prove time or resource finality.
The former `last`, `latest-per-signer`, `latest-per-key` and `register-per-key`
heads are retired and rejected, not aliases.

The state layer interprets interactions admitted by the dialect's multiparty
protocol and roles ([[SPEC-014-role-layer-endpoint-projection]]). Register
ordering does not order protocol execution or replace role authorization.
Each state field chooses its own concurrency policy. Multi-value rules preserve
distinct surviving values without clocks; LWW rules select one survivor using
clock evidence. `:replaces` determines supersession before winner selection for
signer and keyed LWW rules. A keyed delete removes only named observed writes;
unobserved concurrent writes survive. Aggregation rules do not themselves arbitrate by timestamp, though they may
aggregate an earlier LWW-selected field. `bounded-counter` has separate
resource-authorization premises. See
[[hlc-registers#Choosing a state rule]] for examples and the complete rule families.
Convergence does not require clock honesty; interpreting a winner as recent does.

Earlier alternatives remain in Git history. The accepted
replacement contract is ADR-3503, which supersedes ADR-3502's retention decision.
The state specification and corpus advance to major version 4 together. Runtime,
fixtures, authoring, whole-kernel correctness and SEC coverage must agree.
There is no legacy interpreter: pin old signed histories to their previous runtime
or migrate explicitly to a new definition and instance. Controls are REQ-3500–3505;
reviewers read the Orientation, ADR-3503 and validation; implementers use CON-3500.


## Amendment Channels

The user authorizes removal of redundant primary hash selectors and confirms the
existing final content-address tie-break after HLC and signer. This supersedes
ADR-3502's additive retention policy. Earlier alternatives remain in Git history.
No amendment treats timestamps as Byzantine authorization or resource finality.

## REQ-3500: One public register family

The parser, JSON authoring and description MUST expose only `initial` and the
three explicit LWW selectors. `last`, `latest-per-signer`, `latest-per-key` and
`register-per-key` MUST fail closed rather than alias a surviving rule.
Trace: [[SPEC-035-register-semantics#TEST-3500]].

## REQ-3501: Useful, explicit ordering

`lww-register`, `lww-per-signer` and `lww-map` MUST use the total order
`(physical, logical, authenticated signer, content address)`. Content address only
breaks exact HLC/signer ties. A low-level malformed-clock path MUST NOT fall back to
primary hash ordering. HLC generation/update honesty is a host assumption.
Trace: [[SPEC-035-register-semantics#TEST-3501]].

## REQ-3502: Replacement and domains

Signer supersession remains same-verb/same-signer. Keyed supersession and observed
deletes remain key-scoped. Domain-excluded acts contribute neither values nor
replacement evidence. The binder supplies bookkeeping and requires explicit clock
data from callers; it never reads time or invents timestamps.
Trace: [[SPEC-035-register-semantics#TEST-3502]].

## REQ-3503: Opener initialization

`(initial opener key)` MUST install only for the protocol's unique opener verb.
It reads raw distinct accepted candidates without application-data domains.
No candidate or several candidates means Absent. Duplicate receipt of the same
opener preserves the field. Missing payloads do not reduce the candidate count.
Domains MUST read the same raw initializer and cannot filter the opener itself.
Trace: [[SPEC-035-register-semantics#TEST-3500]], [[SPEC-035-register-semantics#TEST-3504]].

## REQ-3504: Versioned implementation and proof evidence

SPEC-019 and the state corpus MUST advance to 4.0.0. Current runtime, JS authoring,
fixtures, whole-clause elaboration and SEC coverage MUST agree on 16 rule heads.
Retired definitions MUST require explicit migration; there is no legacy interpreter
in this runtime. No universal Rust correspondence or resource-classification proof
is implied. Trace: [[SPEC-035-register-semantics#TEST-3503]], [[SPEC-035-register-semantics#TEST-3504]].

## REQ-3505: Proof boundaries

[[SPEC-036-state-kernel-correctness]] MUST cover independent initializer semantics
and the surviving surface vocabulary. [[SPEC-037-state-kernel-sec]] MUST retain
its explicit admission, delivery, fairness and shared-provider premises. Historical
address-selector component lemmas are not current grammar or an installable API.
Trace: [[SPEC-035-register-semantics#TEST-3504]].

## CON-3500: Current wire and authoring surface

```text
(initial opener value-key)
(lww-register verb value-key clock-key)
(lww-per-signer verb value-key clock-key)
(lww-map verb key-key value-key clock-key [delete-verb])
(values verb value-key)                         ; multi-value-register alias
(values-per-key verb key-key value-key [delete]) ; multi-value-map alias
```

LWW clock fields MUST have declared type `hlc`, whose wire string is: `hlc-` + 16 lowercase hex digits + `-` + 8
lowercase hex digits. Clock keys differ from grouping and value keys and are not
routing/compiler fields. JavaScript uses `c.initial`, `c.lwwRegister`,
`c.lwwPerSigner`, `c.lwwMap`, `c.multiValueRegister`, and `c.multiValueMap`.
The JSON authoring contract stays version 3 and rejects removed operation names.
Canonical form stays version 5. New initializer heads change definition identity;
unchanged surviving definitions keep their encoding. Changed acts/references in
fixtures are explicitly re-authored, not reused with mismatching content hashes.

## ADR-3500: Independent kernel correctness

Set invariance permits a consistently wrong interpreter. Independent denotations
and whole-clause elaboration completeness provide the additional guarantee in
[[SPEC-036-state-kernel-correctness]].

## ADR-3501: Keep evidence and transport separate

Clock strings and immutable acts are core inputs. Hosts generate timestamps,
authenticate identities, persist issuance and deliver messages. Resource finality
retains its own separate certification assumptions.

## ADR-3502: Historical additive extension, superseded

The initial implementation retained primary hash selectors beside LWW. The user
rejected that redundant surface. ADR-3503 replaces it; this section grants no
ongoing support to removed heads.

## ADR-3503: One explicit LWW family and opener-only initialization

Status: accepted by user task, 2026-11-06; supersedes retention in ADR-3502.

Remove `last`, `latest-per-signer`, `latest-per-key`, and `register-per-key` from
parsing, installation, authoring and the public typed rule inventory. Keep
`lww-register`, `lww-per-signer`, and `lww-map`, using the already accepted order
`(physical, logical, authenticated signer, content address)`. Content address only
breaks exact clock/signer ties. It is not an alternate application ordering policy.
Clock evidence remains explicit trusted-host data, with declared shape type `hlc`.

Introduce `(initial opener keyword)` and `c.initial(opener, field)`. Installation
requires the protocol's unique opener. The fold returns that act's field, or
Absent if no unique opener candidate exists. This total low-level behavior chooses
no winner from ambiguous evidence. Domains use the same raw-opener initializer.
Valid accepted protocol histories supply at most one opener.

Keep replacement, deletion and conflict-preserving rules unchanged. All migrated
LWW writers declare and carry their clock; no compiler or binder invents one.
Retired names fail closed with a migration diagnostic. Surviving rules keep their
canonical encoding, while `initial` uses its own head and new definition identity.
SPEC-019 and the conformance corpus advance to 4.0.0. Archived evidence for earlier
commits does not validate the new grammar.

Validation must cover obsolete-head rejection, opener-only installation, empty
and ambiguous initializer evidence, clock-primary ordering and exact hash ties,
domain filtering and replacements, shared JS/binding agreement, and revised Lean
whole-clause/SEC coverage. Proofs of the former address selectors remain historical
component lemmas; they do not make retired surface constructs installable.


## TEST-3500: Vocabulary and initialization

Reject retired S-expression and JSON heads. Install opener-only initial fields;
reject other verbs. Check empty, unique, repeated and ambiguous raw evidence,
including a second candidate with no payload. Validates REQ-3500 and REQ-3503.

## TEST-3501: Explicit clock order

A newer HLC MUST beat a greater hash. Exact HLC ties compare signer, then address.
Malformed clock candidates cannot trigger address fallback. Validates REQ-3501.

## TEST-3502: Bookkeeping and domains

Check signer isolation, observed lower-address edits, keyed deletes and domain-
excluded replacements. Superseded admitted replacers retain their references.
Validates REQ-3502.

## TEST-3503: Shared implementations

Re-author and pin corpus version 4, then pass forward/reversed/duplicate delivery,
intent, JS/WASM and shared export checks. Distinguish changed identities from
surviving unchanged definitions. Validates REQ-3504.

## TEST-3504: Proof and mutation audit

Build revised 16-head surface correctness and SEC proofs. Audit assumptions and
standard axioms. Kill initializer winner-selection mutations alongside clock,
replacement, aggregate and SEC mutants. Record independent review and evidence.
Validates REQ-3503, REQ-3504 and REQ-3505.

Plan: [[IMPL-025-register-simplification]]. Earlier implementation evidence
[[register-semantics-implementation-review]] and earlier mutation outputs are
historical; updated validation is recorded in [[register-simplification-verification]].


## ADR-3504: Declare HLC as a shape type

Status: accepted by user task, 2026-11-06. This is part of the unreleased version-4
surface, not a new clock wire representation or arbitration policy.

Add `hlc` to TypeConstraint and the shape grammar. Its validator uses the canonical
HLC recognizer for any field name, including optional/nested fields without state
or LWW rules. LWW clock references MUST resolve to top-level required `hlc` fields;
plain `string`, optional clocks and missing/unknown declarations are rejected.

Declaration compatibility remains exact: `hlc` is not implicitly accepted where
an existing rule specifically requires a `string` declaration.
Canonical clock recognition belongs to TypeConstraint::Hlc. The R7-only shape export
reuses that validator for its LWW clock checks; it owns no parallel string grammar.
Normal R5 shape validation applies the same type independently of state rules.
Schema and description preserve the `hlc` type, and JavaScript/JSON authoring accepts
`clock: 'hlc'`. The wire value remains a canonical string. Changing a declared type
changes the dialect body/hash; existing typed clock inputs and message bodies do
not change. Host generation, advancement and durable persistence remain obligations.

## REQ-3506: Declared HLC shape semantics

The recognized type vocabulary MUST include `hlc`. Required, optional and nested
shape checks MUST recognize the canonical clock string without state/routing
lookups. LWW references MUST require this declared type. Canonicalization, schema,
description, JSON authoring and JS FieldType MUST preserve it. A plain string MUST
NOT silently become an HLC type. Trace: [[SPEC-035-register-semantics#TEST-3505]].

## TEST-3505: HLC type conformance

Check canonical/invalid strings and non-string atoms; required, optional and nested
fields with names other than `clock`; missing required evidence; standalone shapes
without any state clause; signature-bound type identity; schema/authoring/readback;
and rejection of LWW clocks declared string/optional. Kill a type validator that
accepts every string and retain the independent fold/SEC claim boundaries.
Validates REQ-3506. Evidence: [[hlc-type-verification]].
