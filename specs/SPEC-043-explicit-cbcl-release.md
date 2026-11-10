---
id: SPEC-043
title: CBCL Language Editions and Bounded Evolution
status: draft
mode: reference
version: 0.2.1
last-updated: 2026-11-11
owner: CBCL maintainer
---

# CBCL Language Editions and Bounded Evolution

| Field | Value |
|---|---|
| ID | SPEC-043 |
| Title | CBCL Language Editions and Bounded Evolution |
| Source | Issue #32, https://git.anuna.io/anuna-research/cbcl-rs/issues/32 |
| Next actor | Maintainer: review edition and compatibility decisions; implementer: derive a plan after acceptance |
| Scope | Edition design plus compatible Multikey/resource foundations; no edition ratification or release publication |

## Orientation

Foundation work on this branch adds public Multikey conversion and resource-overflow
refusal, with frozen numeric/identity regression cases. Edition selection, signed
parent locks and portable edition upgrades below remain proposed runtime work.

Intent: signed dialects retain their interpretation across implementation upgrades
and long periods without communication. Rare language editions such as `cbcl-1`
are independent of implementation SemVer. New editions preserve old editions.

```text
[bundled definition + dependencies] → [stable bootstrap recognizer]
                                                ↓
[installed identity] ← [bounds + integrity checks] ← [declared edition]
```

Decision: [[SPEC-043-explicit-cbcl-release#ADR-4300]] separates language editions
from software releases. [[SPEC-043-explicit-cbcl-release#ADR-4301]] prefers bounded
self-extension when later vocabulary is expressible in the existing core.

For example, `(define payments (cbcl-1) @author ...)` selects immutable edition-1
rules. A `cbcl-2` implementation must still interpret that definition under those
rules, preserving its original canonical bytes, identities and verdicts. An older
receiver may learn a portable edition-2 extension from bundled definitions; it
cannot learn an unsupported primitive merely from an edition number.

Controls: [[SPEC-043-explicit-cbcl-release#REQ-4300]] requires an explicit edition;
[[SPEC-043-explicit-cbcl-release#REQ-4301]] forbids implicit substitution;
[[SPEC-043-explicit-cbcl-release#REQ-4302]] binds edition and identity;
[[SPEC-043-explicit-cbcl-release#REQ-4303]] pins dependency interpretation;
[[SPEC-043-explicit-cbcl-release#REQ-4304]] preserves sender/receiver agreement;
[[SPEC-043-explicit-cbcl-release#REQ-4305]] prohibits implicit legacy migration;
[[SPEC-043-explicit-cbcl-release#REQ-4306]] requires backward compatibility;
[[SPEC-043-explicit-cbcl-release#REQ-4307]] constrains portable extensions;
[[SPEC-043-explicit-cbcl-release#REQ-4308]] prohibits implicit key reinterpretation;
[[SPEC-043-explicit-cbcl-release#REQ-4309]] refuses resource overflow;
[[SPEC-043-explicit-cbcl-release#REQ-4310]] pins canonical boundary vectors;
[[SPEC-043-explicit-cbcl-release#REQ-4311]] prohibits archive self-authorization.

Open: maintainer ratifies the first language report and compatibility obligations;
implementer derives the plan, manifest schema and extension-verification contract.
Reading paths: authors read declaration and migration; reviewers challenge the
identity and edition decisions; implementers follow each requirement to its test.

## Failure and intent

The failure is unsigned interpretation selection: `(cbcl)` selects a host's
current base dialect. A signed definition can therefore acquire different meaning
after upgrading its interpreter. Issue #32 proposes implementation SemVer as the
selector. Subsequent maintainer direction replaces that coupling with rare,
numbered language editions, analogous to language reports, and requires later
editions to remain compatible with earlier ones.

Long communication delays mean negotiation and online dependency lookup cannot
be prerequisites for interpreting a delivered bundle. Profiles identify meaning;
bundles supply available definitions and evidence. An identifier cannot create
missing implementation capabilities.

## ADR-4300 — Immutable language editions, independent implementation releases

Use `cbcl-1`, `cbcl-2`, and subsequent numbered language editions. There is no
scheduled edition cadence. Implementation fixes, performance improvements and
bindings do not create an edition when specified observable behavior is unchanged.
New dialect vocabularies normally remain ordinary extensions of an existing edition.

Each edition report fixes syntax, evaluation, admission, state rules, canonical
forms, cryptographic identifiers and type/regex/Unicode profiles. A canonical
manifest binds immutable normative artifacts and test vectors by digest. It does
not include derived base/dialect identities: hash the manifest first, derive base
identities second, record both in a separate publication index. This avoids a cycle.
The readable edition identifier has one immutable manifest digest, carried in signed
content and checked against the implementation's trusted edition table. Receipt of
a manifest alone does not authorize a new identifier-to-digest association.

Trace: [[SPEC-043-explicit-cbcl-release#REQ-4300]],
[[SPEC-043-explicit-cbcl-release#REQ-4306]].

## ADR-4301 — Conservative evolution through bounded self-extension

Prefer expressing edition-2 additions as ordinary, content-addressed definitions
over edition 1. A deployment bundle can carry those definitions and their full
dependency closure, allowing an edition-1 receiver to recognize and validate the
extension locally without waiting for a negotiation round trip.

This is a proposed path, not an existing proved edition-upgrade mechanism. Current
R1/R2/R3 checks address recursion, resources and core-name preservation. They do
not alone prove whole-language semantic conservativity, canonical-byte preservation
or identical admission and state observations. Those are separate obligations.

A portable extension can add definitions expressible using existing facilities.
It cannot change its interpreter's atom grammar, canonical encoding, cryptographic
primitives, or meaning of existing operations. A later edition needing such native
additions must retain older interpretation and declare its new native requirements;
an old receiver reports unsupported semantics for those additions. Backward
compatibility does not imply every older implementation can execute newer features.

Trace: [[SPEC-043-explicit-cbcl-release#REQ-4306]],
[[SPEC-043-explicit-cbcl-release#REQ-4307]].

## CON-4300 — Declaration and bootstrap

Recognize the complete bounded S-expression before semantic processing. Structural
selection uses the existing lexical `symbol`, `author`, and `clause` productions:

```ebnf
definition = "(", "define", symbol, parents, author, { clause }, ")" ;
parents = "(", edition, { parent }, ")" ;
edition = "cbcl-", nonzero, { digit } ;
nonzero = "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
digit = "0" | nonzero ;
parent = symbol ;
```

The first parent position selects the edition. Extra edition selectors, missing
selectors and leading-zero spellings reject. Existing input limits apply before
lookup; edition identifiers need no fixed-width integer conversion. Select the
edition before dialect-body recognition, expansion or contract compilation.

Exported definitions carry exactly one `:parent-lock` clause, mapping each custom
parent symbol to its canonical content-addressed self-name; no unused or duplicate
entries are allowed. Empty custom parent sets carry an empty lock. Preparation
resolves authoring aliases and returns pinned definitions for review before signing.
Installation never silently fills a lock. Receivers fetch by pinned identity and
verify its body; local aliases do not determine meaning. Canonical form sorts lock
entries by UTF-8 key and binds keys and addresses. The edition base is selected
from the manifest rather than represented as an author-controlled parent lock.

## ADR-4302 — Self-name, signing bytes and integrity hash

Existing `dialect_name` derives a self-address from canonical content with the
name slot empty; `dialect_hash` hashes signing content including the populated
name. They are distinct hashes. The design must not call both the same identity.

Retain an acyclic construction for the introducing edition: normalize the fully
pinned body, including edition and manifest digest; replace only its designated
name slot with the empty string; hash that projection to derive the self-name;
populate the name; then compute signing bytes and their separate integrity hash.
Signatures and stored integrity metadata are excluded from both preimages. Parent
locks use self-names, never the separate named-form integrity hash. Authored friendly
names are preparation aliases outside the canonical self-name slot.

Do not recursively erase hash-looking strings. Ordinary body data remains committed;
self-references needing the final identity cannot be embedded before hashing. Such
references require an already-defined identity-independent binder, or are rejected.
This proposal does not invent a recursive hash fixed-point mechanism.

Trace: [[SPEC-043-explicit-cbcl-release#REQ-4302]].

## Requirements

### REQ-4300

New-edition installation SHALL require the exact language edition declaration in
[[SPEC-043-explicit-cbcl-release#CON-4300]], independently of package SemVer.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4300]].

### REQ-4301

All installation paths SHALL select the declared edition without substituting
latest, host version or a newer edition. Unknown required semantics SHALL prevent
semantic execution. Hosts may retain or forward bounded opaque content without
claiming semantic acceptance. Installation failure SHALL leave the registry unchanged.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4301]].

### REQ-4302

Edition identifier and manifest digest SHALL be committed by self-name derivation
and signatures using [[SPEC-043-explicit-cbcl-release#ADR-4302]]. A mismatch SHALL
reject even unsigned input. The new signing form SHALL receive an explicit version
allocation; old-edition signed objects SHALL retain their old bytes and identities.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4302]].

### REQ-4303

Dependencies SHALL resolve by pinned self-name, with their original edition-bound
interpretations. Missing or cyclic dependencies SHALL prevent installation.
A later-edition child MAY depend on an earlier-edition parent only through the
published conservative embedding, preserving parent bytes and meaning. An earlier
receiver MAY interpret a portable extension only through its verified older-core
definition. Edition-number ordering alone SHALL NOT authorize either operation.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4303]].

### REQ-4304

Sending, receipt, admission, expansion, state reads and intent binding SHALL use
the installed dialect's bound interpretation consistently. Nested scopes and causal
references SHALL NOT silently reinterpret older objects. Complete dependency and
evidence bundles SHALL permit supported interpretation without online lookup or
negotiation. Resource exhaustion SHALL remain distinct from unsupported semantics
and protocol violations; semantic compatibility does not promise identical host budgets.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4304]].

### REQ-4305

Unversioned legacy definitions SHALL NOT be implicitly assigned a language edition.
Explicit migration SHALL validate against the selected edition and produce new
identities and signatures, preserving historical fixtures. Committed descendants
require reissue when referenced identities change. Legacy replay requires explicit
historical semantics and SHALL NOT silently install into an edition registry.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4305]].

### REQ-4306

Each later edition SHALL preserve earlier-edition valid objects, interpretation,
canonical bytes, identities, signature verification and specified admission/state
results. Invalid earlier-edition objects SHALL NOT become accepted merely because
the host upgraded. A conforming edition-2 implementation SHALL support edition 1;
removing that support precludes claiming full edition-2 conformance. New syntax
requires explicit edition selection or validated dialect scope and SHALL NOT change
the interpretation of existing content. An incompatible redesign cannot be declared
a compatible successor by incrementing the edition number.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4306]].

### REQ-4307

Portable edition extensions SHALL ship their complete content-addressed definition
closure and pass the older core's recognition, integrity and resource checks before
installation. They SHALL NOT redefine old primitives or bypass host authorization.
Their newer native and older expanded interpretations SHALL agree on observable
semantics, including admission and state. Expansion bounds and resulting addresses
SHALL be explicitly specified; equivalent behavior alone does not prove equal bytes.
Unsupported native additions SHALL NOT be presented as portable definitions.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4307]].

## OBS-4300 — Diagnostics and ownership

Core/parser expose edition, manifest digest, self-name and separate integrity hash
through inspection. Structured errors distinguish missing/invalid/unsupported
edition, manifest mismatch, dependency incompatibility and resource exhaustion.
Bindings preserve codes. Hosts own transport, archival retention, fetching and
writes; retaining a frame never claims its semantic acceptance. Every requirement
above is observable through inspection, these errors and its traced test.

## Acceptance design

Future tests, not executed runtime evidence. Each case also traces to
[[SPEC-043-explicit-cbcl-release#OBS-4300]].

### TEST-4300

Accept `cbcl-1`; reject missing, duplicate and malformed edition selectors.
Changing implementation SemVer does not change selection.

### TEST-4301

Unsupported native semantics reject without registry mutation or fallback.
Opaque forwarding never causes admission or execution.

### TEST-4302

Compute self-name in one pass with the designated slot blank; fill it and verify
signatures. Recompute the same self-name after serialization. Ordinary body strings
are not blanked. Edition, manifest or parent changes alter identity; forged names
reject. Distinguish the self-name from the named-form integrity hash.

### TEST-4303

Verify same-edition and published conservative cross-edition graphs. Reject missing,
cyclic and unverified crossings. Transfer a child between hosts with different alias
bindings and obtain identical dependencies from its signed locks.

### TEST-4304

Disconnect a receiver from the network, upgrade its implementation and deliver an
archived complete bundle. Preserve original interpretation, or explicitly report
unsupported semantics or insufficient resources; never request negotiation to select
meaning. Exercise sender, receiver, nested scopes, causal evidence and bindings.

### TEST-4305

Reject implicit legacy assignment. Explicit migration emits reviewed new definitions,
address maps and signature requirements without modifying original corpus bytes.

### TEST-4306

Run frozen positive and negative edition-1 vectors through edition-1 and edition-2
implementations. Compare bytes, identities, signature outcomes, admission and state.
Acceptance requires a general conservative-embedding argument alongside regression
vectors; finite examples alone do not prove universal backward compatibility.

### TEST-4307

An offline edition-1 receiver installs a bundled portable extension within its bounds
and agrees with its specified native interpretation. Reject core redefinitions,
missing closure, excessive expansion and attempts to disguise new parser primitives
as teachable vocabulary. Mutate these guards and show the corresponding tests fail.

## Migration and publication

First ratify the edition-1 report, immutable manifest and frozen vectors. Introduce
explicit selection and alias-to-self-name preparation across Rust and bindings.
Publish migration tools that emit proposed definitions without overwriting originals.
Edition publication is independent of package tags and has no scheduled cadence.

Later reports must carry conservative-embedding evidence and native requirements.
Preserve older executable interpretations and artifacts. Teaching definitions does
not grant permission to execute effects, spend resources or install untrusted code.

## Amendment Channels

The maintainer may amend this draft by reviewed repository change or explicit task
instruction recorded here. No amendment may silently reassign published identifiers,
rewrite old signed content or call incompatible meaning backward compatible.

## Open decisions and review status

Maintainer owns edition-1 report ratification. Implementer owns the plan, concrete
manifest/lock schema, resource accounting and portable-extension proof contract.
The native/portable equivalence mechanism remains proposed, not implemented or
proved. Earlier independent review covered the superseded release-based proposal;
the edition-based revision received a separate Orientation-only comprehension
review, correctly predicting old/new behavior and the unimplemented runtime boundary.
Adversarial foundation review found an unsafe implicit Multikey adapter and missing
literal identity vectors; both were corrected before acceptance. Runtime edition
and archive gates remain deferred rather than approved by that review.

## Synthesis record

Issue #32 supplied the stable-interpretation intent. Maintainer discussion then
required language-report cadence, numbered editions, backward compatibility and
consideration of bounded self-extension. Related current semantics are described
in [[SPEC-040-numeric-and-refinement-types]] and
[[SPEC-042-boundary-canonicalisation]]. Existing self-name code was inspected to
identify its empty-name preimage and distinguish it from named signing-form hashes.
The edition runtime remains a proposal; compatible foundation changes are governed
by the implementation requirements below.


## Longevity audit — implementation observations, 2026-11-10

This is a source inspection, not a full security audit or proof of behavior.
The next actor is the edition designer: classify each item before ratifying
edition 1, then derive implementation work and executable acceptance evidence.

- Cryptographic agility is incomplete: `multihash.rs` accepts only SHA2-256 and
  `typed_addr.rs` fixes 32-byte Merkle nodes. Signature identity represents unknown
  suites but `attest.rs` implements only Ed25519 dispatch. Algorithm replacement,
  archival evidence renewal and principal continuity require separate policies;
  backward readability must not mean indefinite security acceptance.
- Canonical forms are current-global constants (dialect form 7, address form 2)
  rather than an edition dispatch table. The self-name and named-form integrity
  hash are separate. Freeze their contracts and verify old bytes across upgrades.
- Float text uses Rust `f64` parsing/display; regex compilation and work accounting
  use dependency-produced NFA structure. Dependency/compiler upgrades must not
  silently change normative canonical bytes or resource-profile acceptance.
- Contract profile pins Unicode 16 and hard resource caps. Retain old Unicode
  tables; separate semantics, portable work definitions and host admission budgets.
  `ResourceBounds` also constrains verification milliseconds to at most 1000;
  wall time cannot substitute for a portable semantic cost model.
- Registry ancestry uses host-local names and skips unresolved names. Pin parent
  identities and edition-bound interpretation before signature preparation.
- Bounded vocabulary extension does not make new atom syntax, state rule heads,
  cryptographic primitives or canonical encodings portable. Decide the minimum
  enduring core and require conservative-extension evidence for later editions.
- Message/evidence stores and pending queues are not a complete archival delivery
  contract. Specify dependency bundles, durable evidence retention, trust context
  and recovery separately from live buffering/TTL policy.
- Normative authority is unsettled: grammar comments defer to the IETF draft and
  then sources; the draft still contains historical address spellings. Ratify a
  consistent language report plus preserved vectors rather than making current
  Rust behavior the final authority. Existing Lean/model and native differential
  evidence are useful but do not establish universal implementation refinement.

Fixed-width integers and a pinned Unicode edition are not inherently longevity
failures: explicit limits can be durable. The hazards are accidental host dependence,
undocumented changes and the inability to extend within those limits safely.

## CON-4301 — Public Multikey adapter

Use the public-key payload encoding in W3C Controlled Identifiers 1.0, section
2.2.2: https://www.w3.org/TR/cid-1.0/#multikey. This implements its payload format,
not a complete controlled identifier document or a `did:key` method. Reference
codec assignments: https://github.com/multiformats/multicodec/blob/master/table.csv.

```ebnf
multikey = "z", base58btc-character, { base58btc-character } ;
base58btc-character = ? Bitcoin base58 alphabet, excluding 0, O, I and l ? ;
public-key-payload = minimal-unsigned-varint-codec, codec-specific-public-bytes ;
key-adapter = multikey ; (* explicit from_multikey API only *)
```

Recognize the complete bounded string and binary payload before returning a key.
Only Ed25519, X25519, compressed P-256 and compressed P-384 public-key payloads
are recognized initially. Reject unknown codecs, private-key codecs, nonminimal
varints, empty payloads, wrong lengths, invalid compressed EC prefix, alternative
multibases and trailing bytes. Limit text to 256 bytes before base58 decoding;
all recognized payloads fit within that bound. Structural recognition does not
assert mathematical point validity, possession, authorization or trust. Hosts must
perform cryptographic key validation when constructing their verifier.

`KeyId::from_multikey` is an explicit API adapter into existing suite-typed key identity.
Only Ed25519 has a supported signing suite in this implementation; other parsed
public-key kinds cannot enter Ed25519 sign/verify through that adapter. Ed25519
maps to `@ed25519:<canonical-multikey>` without altering that spelling's existing
identity or signature preimage. Existing `@alice` spellings do not change meaning.
No parser grammar or existing `KeyId::parse` interpretation is changed. In
particular, existing `@multikey:z...` remains an unknown-suite principal; callers
request public-key interpretation through the separate constructor. Rotation to another key remains a different principal unless
an explicitly authenticated host policy relates them.

### REQ-4308

The public Multikey implementation SHALL enforce
[[SPEC-043-explicit-cbcl-release#CON-4301]] and preserve existing canonical identity
and signature behavior. It SHALL NOT treat key bytes as proof of possession,
authorization, safe rotation or support for a signature algorithm.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4308]].

### TEST-4308

Decode independently sourced W3C vectors and round-trip recognized codec payloads.
Reject nonminimal/overflowing varints, private/unknown codecs, invalid alphabet,
wrong lengths, unsupported multibases and oversized text. Explicit constructor results
must deduplicate with the existing suite-explicit identity. Non-signing/unsupported
keys must reject in the adapter; existing attestation bytes must remain identical.
Deliberately bypass codec/length checks and verify tests fail.

### REQ-4309

Portable resource arithmetic SHALL refuse overflow deterministically, independent
of debug/release compilation, while preserving existing strict-bound semantics.
Host wall-clock and retention limits SHALL NOT be specified as language meaning.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4309]].

### TEST-4309

Exercise exact depth/expansion boundaries and `u32::MAX` arithmetic. Debug and
release builds must refuse overflow rather than panic or accept a wrapped result.

### REQ-4310

Existing canonical float, decimal and self-name bytes SHALL be pinned by boundary
vectors. A future implementation or dependency upgrade SHALL reproduce the selected
profile's vectors and normative conversion rules before claiming compatibility.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4310]].

### TEST-4310

Cover signed zero, subnormal/maximum binary64 values, adjacent representable floats,
integer-looking floats and normalized arbitrary-precision decimals. Verify dialect
self-name derives from an empty-name projection and remains unchanged after filling
that name, while the named-form integrity hash is a separate deterministic value.

## Archival and trust contract

An offline archival package must identify the interpretation manifest and include
all dialect definitions, parent locks, reachable causal evidence and the public
verification material needed by its claims. A compact checkpoint must include the
certificates and coverage assumptions it relies on; it is not a substitute for
unavailable evidence by assertion. Validate all addresses, signatures and closure
before semantic admission; a supplied manifest cannot install arbitrary native code.

The host records trust anchors, signer authorizations and historical verification
policy separately from cryptographic bytes. Key expiry/revocation and algorithm
retirement are evaluated against explicit policy and available evidence, not the
receiver's silently changing current key database. Historical readability does not
promise indefinite trust or operation permission. Renewal certificates may bind
old evidence to new algorithms before retirement; their authority and preservation
must be explicit, and replacing an old hash prefix is never renewal.

Storage retention and transport scheduling remain host responsibilities. A pending
queue's TTL or capacity eviction is a recoverable operational outcome; it cannot
rewrite accepted history or establish that a missing predecessor never existed.
Acceptance requires offline archive recovery under a fresh installation, with no
alias registry, network lookup or negotiation available. Missing material produces
an explicit incomplete/unsupported result, never fabricated semantic success.

## Normative authority and edition ratification

A ratified language report and its immutable profile artifacts define behavior;
implementations and generated grammar are evidence of conformance, not overriding
authorities. Existing historical editions retain their reports and vectors.
Conflicts found before ratification must be resolved explicitly in the report,
grammar, model and native tests. Report errata may clarify an existing rule but
cannot silently change previously specified bytes or meaning. Security restrictions
may refuse execution under local policy without pretending the language changed.

The implementation ledger and audit decisions are
[[IMPL-043-longevity]]. No `cbcl-1` production conformance claim is made here.


### REQ-4311

A production offline-recovery claim SHALL select trust policy from locally trusted
configuration or a separately authenticated policy authority, never from an archive's
own assertion. Historical expiry or revocation claims SHALL name authenticated
historical evidence and its policy authority. If policy, historical timing or
required revocation evidence is unavailable, the host SHALL expose insufficient
trust evidence separately from syntax validity and SHALL NOT assert historical
authorization. Local policy may refuse effects while preserving original meaning.
Trace: [[SPEC-043-explicit-cbcl-release#TEST-4311]].

### TEST-4311

Recover a complete archive in a fresh offline installation using independently
provisioned trust anchors. Reject archive-supplied self-authorization, altered
policy, missing certificates and unsupported primitives. Missing authenticated
historical timing or revocation evidence reports insufficient trust evidence.
Verify closure recovery separately from authorization; a complete hash DAG alone
cannot establish who was authorized to issue an act.

### Deferred edition-runtime gates

Owner: edition implementer, reviewed by maintainer. Complete the signed selector,
parent-lock runtime and multi-edition dispatch before claiming installation support
for `cbcl-1`. Their governing tests remain
[[SPEC-043-explicit-cbcl-release#TEST-4300]] through
[[SPEC-043-explicit-cbcl-release#TEST-4307]]. Before claiming portable edition-2
support, specify the observable semantics and a mapping between native and expanded
identities; neither equivalent effects nor bounded expansion implies equal hashes.

Owner: archive implementer, reviewed by host trust-policy maintainer. Complete
[[SPEC-043-explicit-cbcl-release#TEST-4311]] before claiming archival recovery with
historical authorization. The existing causal closure recovery is a lower layer;
no century-scale trust or durable retention guarantee is claimed by these foundation
changes. These gates are deferred explicitly because no edition report, native
extension embedding or authenticated archive-policy format is yet ratified.


## CON-4302 — Portable canonical float selection

For a finite nonzero binary64 value, use its exact positive rational magnitude.
At significant precision `p`, use decimal-grid spacing
`10^(floor(log10(abs(value))) - p + 1)`. For increasing `p`, consider the
bounding decimal-grid candidates around the exact rational. Select the first precision with a candidate
that converts to the same binary64 bits using IEEE nearest/ties-to-even parsing.
Among successful candidates at that precision choose the closest rational value;
if equally close, choose the greater magnitude. Render in fixed-point decimal
notation with redundant fractional trailing zeroes removed and `.0` retained
for integral floats. Restore the sign; both zero signs canonicalize to `0.0`.

The decimal tie rule is intentionally distinct from binary64 parsing's tie rule.
For example `2^-25` is exactly halfway between decimal candidates ending in
`...312` and `...313`; the current profile selects
`0.000000029802322387695313`. This selection must not be left to an unspecified
formatter choice. The Rust implementation currently matches this rule; an exact
BigUint rational oracle checks every binary exponent boundary and neighbors,
frozen tie cases and generated finite bit patterns. These checks are conformance
evidence, not a proof for all binary64 values or verification of decimal parsing.

Trace: [[SPEC-043-explicit-cbcl-release#REQ-4310]],
[[SPEC-043-explicit-cbcl-release#TEST-4310]].


## ADR-4303 — Retain no_std and the W3C public-key payload

The maintainer explicitly selected preservation of `no_std` and the W3C payload
format on 2026-11-11 after considering the published `multi-key` crate. This
supersedes the interim suggestion to adopt its top-level container grammar.

The crate is not a wire-compatible replacement for
[[SPEC-043-explicit-cbcl-release#CON-4301]]. W3C public-key payloads contain a
key-codec varint followed directly by public-key bytes. The crate's container
instead carries a Multikey sigil, key codec, length-prefixed comment, attribute
count and length-prefixed attributes. Substituting that grammar would change the
accepted payloads and the key identities derived from them.

Published-source inspection found that `multi-key` 3.1.0 uses `std` and requires
Rust 1.99; 2.1.0 also uses `std` and requires Rust 1.96. The older 1.0.2 container
also imports `std`. Disabling default features does not make these releases
`no_std`. These are dependency-evaluation observations, not permanent claims about
future upstream releases. Sources: https://docs.rs/crate/multi-key/3.1.0/source/Cargo.toml
and https://docs.rs/crate/multi-key/3.1.0/source/src/mk.rs.

Decision: retain the small W3C public-key boundary, using the existing `bs58` and
`unsigned-varint` dependencies for base encoding and varint recognition. CBCL owns
only its public-codec allowlist, input bounds, key-shape checks and explicit identity
conversion policy. It does not implement cryptographic algorithms or the alternative
key container. A future host keystore may use `multi-key` behind an explicit adapter,
but neither host integration nor container-format migration is part of this choice.

Trace: [[SPEC-043-explicit-cbcl-release#REQ-4308]],
[[SPEC-043-explicit-cbcl-release#TEST-4308]].
