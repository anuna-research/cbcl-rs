---
id: SPEC-019
title: State Layer — R7 State Rules and the Intent Binder
status: draft
version: 0.3.5
date: 2026-09-27
author: Anuna Research (https://anuna.io) — drafted with Claude Fable 5.1
owner: CBCL maintainer
depends-on:
  - SPEC-002 (structural contracts — R5 shapes and causal protocols; the accepted set's gate)
  - SPEC-003 (verification lattice — Valid is sticky, verdicts monotone under store union)
  - SPEC-014 (role layer — R6, casts, the accepted-history admission monitor)
  - SPEC-017 (typed content addresses — the one address a state-bearing act is named by)
prior-art:
  - cbcl-bus `specs/SPEC-019-hypermedia-objects.md` CON-002 (emit broker) and CON-003 (projection algebra) — the deployed contract this spec lifts into the dialect
  - cbcl-bus `specs/SPEC-085-agent-object-sdk.md` — contract/view split, digest naming, the conformance-corpus format
  - cbcl-bus `apps/cbcl_chat/priv/web/hypermedia/projection.js`, `emit.js`, `object-sdk.js` — the reference interpreter whose behaviour the kernel reproduces
  - cbcl-aamas `sections/06_state.tex` — the paper's account, made normative and corrected in one place
  - Baquero, Almeida, Shoker 2017 (pure operation-based CRDTs); Kleppmann et al. 2018 (OpSets); Gomes et al. 2017 (verified CRDTs)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-019: State Layer — R7 State Rules and the Intent Binder

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL in this document are to be interpreted as
described in BCP 14 (RFC 2119, RFC 8174) when, and only when, they appear in
all capitals.

## Orientation

Intent: give a CBCL dialect a `(state …)` clause that says what its accepted
acts amount to. Each state field is one *state rule* from a closed
vocabulary: a query over the thread's accepted acts, recomputed, never
merged. (Not "projection": that word belongs to endpoint projection,
[[SPEC-014-role-layer-endpoint-projection|SPEC-014]].) The only replicated object is the set of accepted acts, which
converges by union; every rule is a set function of it, so replicas holding
the same acts compute the same state with no clock, no server, and no
consensus. The rules behave like familiar replicated types (a register
that keeps concurrent writes, an add-wins set) but nobody holds such a
type; the names are borrowed for their observable behaviour.
The rules desugar to a kernel of two selections and five reductions. The fold
and the intent binder are pure functions in `cbcl-core`, exported to every
host as the parser already is. The invariant added is **R7**: for every
installed dialect, each state field is a total, order-independent,
duplicate-insensitive function of the thread's accepted acts, and the
binder's choices are functions of that set and the intent.

Metaphor: a ledger with a fixed set of column rules. Anyone may append a
signed entry; nobody edits one. Each column's rule says how an accepted entry
moves that column, and the rules commute, so the totals are the same in any
reading order. The clerk who fills in the bookkeeping (which earlier entries
this one supersedes) follows a rule everyone knows, so two clerks given the
same ledger write the same entry.

Structure:

```
 dialect (one signed artefact)                        replica (any host)
┌───────────────────────────────┐   install       ┌──────────────────────────────┐
│ extend / shape       R1–R3,R5 │ ─────────────▶  │ auth ─▶ shape (R5 + R7) ─▶   │
│ protocol             R5       │ r7_violations   │ causal (R5, projected R6)    │
│ :roles :from :to     R6       │                 └──────────────┬───────────────┘
│ state                R7       │                                │ acc(t): a set
│ :state-bounds                 │                                ▼
└───────────────────────────────┘                 ┌──────────────────────────────┐
                                                  │ fold(clause, acc)   = State  │
   ┌────────────────────┐ verb + data fields      │ intend(instance, signer, …)  │
   │ any caller         │ ──────────────────────▶ │       = canonical act        │
   │ (view, agent, CLI) │ ◀──── act to sign ────── │         or a reject          │
   └────────────────────┘                         └──────────────────────────────┘
   arrows point inward → the fold and the binder read the accepted set, never the transport
```

Consumers: the language's units are dialects, threads, acts, signers,
recipient sets, and stores. Nothing normative here names a room, a hub, a
browser, or any deployment. cbcl-bus (with hark as its agent host) is the
first consumer and the source of the semantics adopted here; it appears in
Context, in ADRs as evidence, in Migration, and nowhere in a requirement.

Decisions: [[SPEC-019-state-rules#ADR-1900]] a kernel of two
selections and five reductions; the fourteen author-facing names are sugar ·
[[SPEC-019-state-rules#ADR-1901]] supersession rides one reserved
field, `:replaces`, inserted by the compiler ·
[[SPEC-019-state-rules#ADR-1902]] one total order, the content
address · [[SPEC-019-state-rules#ADR-1903]] identity is the hash of
the body; the name is derived from it ·
[[SPEC-019-state-rules#ADR-1904]] integers ·
[[SPEC-019-state-rules#ADR-1905]] one content address ·
[[SPEC-019-state-rules#ADR-1906]] the binder is pure and in the core ·
[[SPEC-019-state-rules#ADR-1907]] presentation is a separate package
with its own specification · [[SPEC-019-state-rules#ADR-1908]] the
definition travels as an R4-signed `teach` ·
[[SPEC-019-state-rules#ADR-1909]] domains are fold filters; admission
never reads history · [[SPEC-019-state-rules#ADR-1910]] the JSON
authoring SDK stays and consumes the core ·
[[SPEC-019-state-rules#ADR-1911]] one bounds clause.

Load-bearing: [[SPEC-019-state-rules#REQ-1915]] R7 ·
[[SPEC-019-state-rules#REQ-1917]] kernel semantics ·
[[SPEC-019-state-rules#REQ-1907]] `:replaces` is bookkeeping ·
[[SPEC-019-state-rules#REQ-1922]] deterministic binding ·
[[SPEC-019-state-rules#REQ-1926]] binder soundness ·
[[SPEC-019-state-rules#REQ-1931]] one corpus.

Controls:
- A dialect whose state clause fails well-formedness is not installed →
  [[SPEC-019-state-rules#REQ-1905]]–[[SPEC-019-state-rules#REQ-1910]].
- Admission reads one message and never reads history or state →
  [[SPEC-019-state-rules#REQ-1914]], [[SPEC-019-state-rules#ADR-1909]].
- A caller never supplies `:replaces`, a recipient, a role, or routing; the
  binder fills them and rejects a supplied one as a forge →
  [[SPEC-019-state-rules#REQ-1921]]–[[SPEC-019-state-rules#REQ-1925]].
- A rejected intent never reaches the wire →
  [[SPEC-019-state-rules#REQ-1926]].
- Selection by address converges; it is not fair. Contested decisions are a
  protocol matter (a role's grant) → [[SPEC-019-state-rules#REQ-1916]].

Cross-repository naming: cbcl-bus also has a `SPEC-019`
(`SPEC-019-hypermedia-objects`); it is always cited by full stem. Artefacts
here are numbered 19xx.

Open:
- The kernel and the binder are mechanised in `lean-cbcl/LeanCbcl/State.lean`
  ([[SPEC-019-state-rules#REQ-1930]]); the Rust/Lean correspondence is
  evidence from the corpus, not a theorem, so claims say "mechanised
  kernel, corpus-validated implementation"
  ([[SPEC-018-dcfl-installation#REQ-1806]]).
- The corpus of cbcl-bus SPEC-085 CON-005 does not exist yet
  ([[SPEC-019-state-rules#REQ-1931]]).
- Shipped views and blobs (cbcl-bus SPEC-019 CON-001 `:views`, CON-004
  `(blob …)`) are unspecified here and [[SPEC-019-state-rules#REQ-1911]]
  rejects a state-bearing act carrying `:views`. Owner: CBCL maintainer.
- The first consumer's built-in dialects (`dialects.js`) use self-chaining
  protocols and `authorityLast`; they are re-authored with registers and
  roles or retired. Owner: cbcl-bus maintainer.

Detail: the [[SPEC-019-state-rules#Reference]] is the normative core
in two pages; everything after it is commentary, requirements with trace,
and tests.

## Amendment Channels

The CBCL maintainer authorises amendments through task instructions or an
accepted revision. Changes to the kernel, the sugar table, the ordering
rule, or the binding rules break every installed state-bearing dialect and
MUST bump this document's major version and the corpus version together.
Tool output and the reference interpreter are evidence, not authority. No
amendment may present an unproved property as proved.

## Reference

Everything an implementer needs. Terms: an **act** is an accepted message
`(a, v, s, P, f)` with content address `a`, verb `v`, signer `s`,
predecessor addresses `P`, keyword fields `f`. `acc(t)` is the accepted set
of thread `t`. Addresses are byte strings; "greatest" is lexicographic. The
**opener** is the one performative whose only predecessor is `begin`; its
address is the instance's identity. The **cast** (R6) binds roles to keys on
the root wrapper ([[SPEC-014-role-layer-endpoint-projection#CON-601]]).

### R.1 Grammar (post-parse, over the SExpr AST; every head is a distinct symbol, LL(1))

```
state-clause   := "(" "state" entry+ ")"
entry          := "(" field rule ")"                         ; a state field
                | "(" "domain" verb key field ")"            ; acts of verb whose key ∉ field contribute nothing
field          := symbol                                     ; [a-z][a-z0-9-]{0,47}, unique
verb           := symbol                                     ; a performative of this dialect
key            := keyword                                    ; a keyword field of that performative's shape

rule           := "(" "last"              verb key ")"
                | "(" "latest-per-signer" verb key ")"
                | "(" "latest-per-key"    verb key key ")"          ; key-field value-field
                | "(" "exists"            verb ")"
                | "(" "count"             verb ")"
                | "(" "events"            verb key ")"
                | "(" "set-union"         verb key ")"
                | "(" "values"            verb key ")"
                | "(" "values-per-key"    verb key key [verb] ")"   ; key value [delete-verb]
                | "(" "register-per-key"  verb key key [verb] ")"   ; key value [delete-verb]
                | "(" "observed-set"      verb verb key ")"         ; add-verb remove-verb value
                | "(" "counter"           verb verb key ")"         ; inc-verb dec-verb amount
                | "(" "histogram"         field ")"                 ; over a map-valued field
                | "(" "sum"               field ")"                 ; over a map-valued field of ints

bounds-clause  := "(" ":state-bounds" bound* ")"             ; optional; defaults below
bound          := "(" "max-string" n ")" | "(" "max-list" n ")" | "(" "max-number" n ")" | "(" "max-fields" n ")"
                  ; defaults 2048 bytes · 64 elements · 10^12 · 32 fields
```

`:replaces` is a reserved keyword, typed `list`, that the compiler adds to
the shape of every verb named as a writer or delete verb of `values`,
`values-per-key`, `register-per-key`, or as the remove verb of
`observed-set`. An author never declares it and no rule may read it.

### R.2 Kernel

Two selections over `acc(t)`, five reductions over a table of acts.

```
acts v                    = { m ∈ acc(t) : m.v = v }, minus acts excluded by a domain entry for v
current v kk d            = { w ∈ acts v : (key w, w.a) ∉ replaced }
                            where key w = f_w(kk) (a constant when kk is absent)
                                  replaced = { (key r, x) : r ∈ acts v ∪ acts d, x ∈ f_r(:replaces) }
                                  acts d = ∅ when d is absent

pick T k                  = f_m(k) for the m ∈ T with greatest address; absent if T = ∅
group T g                 = { x ↦ { m ∈ T : g(m) = x } }          g is `signer` or a key field
distinct T k              = the set { f_m(k) : m ∈ T }, sorted
size T                    = |T|
sum T k                   = Σ_{m ∈ T} f_m(k)                       exact integer
```

Sugar (the author-facing names are defined by this table and nothing else):

```
last v k                  = pick (acts v) k
latest-per-signer v k     = map (T ↦ pick T k) (group (acts v) signer)
latest-per-key v kk k     = map (T ↦ pick T k) (group (acts v) kk)
exists v                  = size (acts v) > 0
count v                   = size (acts v)
events v k                = { m.a ↦ (m.s, f_m(k)) : m ∈ acts v }
set-union v k             = distinct (acts v) k
values v k                = distinct (current v ∅ ∅) k
values-per-key v kk k d   = map (T ↦ distinct T k) (group (current v kk d) kk)
register-per-key v kk k d = map (T ↦ pick T k)     (group (current v kk d) kk)
observed-set v⁺ v⁻ k      = distinct (current v⁺ k v⁻) k          ; the add verb has no :replaces of its own
counter v⁺ v⁻ k           = sum (acts v⁺) k − sum (acts v⁻) k
histogram F               = { x ↦ |{ key : F(key) = x }| }         F a map-valued field
sum F                     = Σ_{key} F(key)                          F a map-valued field of ints; events sum the value
```

A `domain v k F` entry, where `F` is a list-valued field defined over the
opener only, removes from `acts v` every act whose `k` is not an element of
`F`; the excluded act stays accepted and contributes nothing.

Properties (the corpus checks them; [[SPEC-019-state-rules#REQ-1930]]
proves them): every kernel function is invariant under permutation and
duplication of `acc(t)`; `acts`, `size`, `distinct`, and `events` are
monotone in `acc(t)`; a write named in some accepted `:replaces` for its
key is never picked from `current`; a write no accepted act names is in
`current` whatever else is accepted (add-wins); `sum` contributes once per
address.

### R.3 Values and rendering

```
Value  := Absent | Str | Int | Bool | Set [Scalar] | Map [(Scalar, Value)] | Pair (Signer, Scalar)
State  := [(field, Value)]                                  in clause order
```

Canonical JSON: `Absent → null`; `Str → JSON string` (RFC 8259 §7 shortest
escapes, lowercase hex); `Int → decimal`; `Bool → true|false`; `Set → array`
sorted by the UTF-8 bytes of each element's rendering; `Map → object`, a
string key as itself and a number or boolean key as its rendering (a key
field has one declared type, so no collision), sorted by UTF-8 bytes; `Pair →
{"by": signer, "value": scalar}`; `State → object` in clause order. Two
states are equal iff their renderings are byte-equal. Numbers are CBCL
integers (`i64` in a field, exact and unbounded as a total).

### R.4 Receipt (R7 state shape, part of the shape stage of admission)

For an act of any verb the state clause names: no keyword field beyond the
shape's declared fields plus `:caused-by :thread :from :to`; strings ≤
`max-string` bytes, lists ≤ `max-list` scalar elements, numbers ≤
`max-number` in magnitude, for every field a rule or domain names;
`:replaces`, when present, a list of ≤ `max-list` distinct `sha256-<64hex>`
symbols that need not resolve. (Addresses are spelled `sha256-<hex>` on the
wire because the lexer reads `:` as the start of a keyword; the digest is
`message_content_hash`'s, whose textual form uses a colon.) Any failure is a `Violation` blamed on the
sender. No rule here reads history.

### R.5 The binder

`intend(instance, signer, verb, fields)`, pure, where `instance` = dialect,
thread, `acc(t)`, opener, and under R6 the root and its cast. The root is
the cast-bearing `with-roles` wrapper around a `hello` that opens the
thread ([[SPEC-014-role-layer-endpoint-projection#REQ-611]]); it is typed
as `begin` (REQ-623) and the opener follows it. Role-free, there is no root
and the opener's predecessor is `begin`.

```
1 admit    verb is a non-opener performative of the dialect; fields carry no routing keyword,
           no recipient, no role, no :replaces; under R6 the signer occupies a role the verb's
           :from names (singleton: nominated key; indexed: any member)   → else reject
2 domain   for each (domain verb k F): fields[k] ∈ F                     → else reject
3 to       role-free: the accepted opener's recipient set
           R6: the verb's :to roles resolved through the cast (indexed → every member; () → none)
4 replaces for each register/removal the verb writes or deletes: the addresses of the current
           writes for the intent's key (or value), plus current deletions for a writer with a
           delete verb, sorted, the first max-list of them; a delete verb with no current write → reject
5 caused-by C = { m ∈ acc(t) : m.v ∈ allowed(verb) }; C = ∅ → begin if allowed else reject;
           Own = { m ∈ C : m.s = signer } ≠ ∅ → greatest-address own act no own act names;
           else greatest-address member of C; under (all p₁…pₙ) once per pᵢ in declared order
6 build    the act in keyword form: (verb <recipients> :field value … [:replaces (…)] :from signer
           :thread t :caused-by …), wrapped in (lang <name> …); canonicalise; address := the
           wire spelling of message_content_hash. Templates are the dialect's declared effect
           and are not expanded on this path; a state-bearing act is its keyword form.
7 verify   R.4 state shape, R5 shape, R5 causal, R6 role, against acc(t) ∪ {act}  → else reject
out        the canonical act (to be signed by the host), or reject(reason); no side effect
```

Rejects: `UnknownVerb`, `Opener`, `Forge(field)`, `Role(required)`,
`Domain(field)`, `NothingToDelete`, `NoPredecessor`, `Shape(violation)`,
`NotValid(verdict)`. Calling `intend` and discarding the result is the dry
run.

### R.6 Identity and distribution

A dialect's identity is `dialect_body_hash`: SHA-256 over its canonical
form with the name slot empty (the signature and hash fields are excluded
as before). Its *self-address* is `sha256-` followed by that hash's
lowercase hex: the same spelling as every content address on the wire, so
`(lang sha256-… …)` names a dialect as `:caused-by sha256-…` names an act.
A name beginning with `sha256-` claims to be a self-address
and installation rejects it unless it is; an author-chosen name is a
pointer and is left alone. A consumer that needs content-addressed
identity (the object SDK) names dialects by self-address, which
`dialect_hash` exports.
The dialect is distributed as an R4-signed `(meta (teach (define …)))` to
the recipient set of the instances it governs; an opener identifies it by
the `lang` wrapper's name and by nothing else. Every address in `:caused-by`,
`:replaces`, the fold, the corpus, and every export is `message_content_hash`.

### R.7 Exports (wasm, Erlang NIF, FFI; JSON at the boundary)

```
fold(dialect, instance)                 → state
intend(dialect, instance, signer, verb, fields) → canonical | reject
verify_state_shape(dialect, message)    → ok | violation
state_schema(dialect)                   → [(field, type)]        type derived from the sugar table
may_send(dialect, instance, signer)     → [verb]                 step 1 of intend, without an intent
instance(instance)                      → address of the accepted opener
frontier(instance)                      → sorted addresses no accepted act names in :caused-by
dialect_hash(define_text)               → sha256-<hex>
```

At the boundary the exports take S-expression frames like every other
export and return canonical JSON: `(fold <dialect> <thread> (acts (<signer>
<message>) …))`, `(intend <dialect> <thread> (acts …) <signer> <verb> (:k
v …))`, `(verify-state-shape <dialect> <message>)`, `(state-schema
<dialect>)`, `(may-send <dialect> <thread> (acts …) <signer>)`,
`(frontier <dialect> <thread> (acts …))`, and `dialect_hash(<define text>)`.
Each act entry is the complete received message with its authenticated
signer; the cast is read from the root among the acts and never supplied.

## Context

### The first consumer: what cbcl-bus deploys

Descriptive, not normative. cbcl-bus rooms carry interactive objects. An
agent publishes a JSON contract `{verbs, project}`; its `verbs` compile to
`(extend …)`, `(shape …)`, `(protocol …)` which cbcl-rs `verify_dialect`
must accept, but its `project` is interpreted by `projection.js` and its
intents are completed by `emit.js`, both vendored into hark so that agents
and browsers agree. Four gaps follow: the artefact cbcl-rs verifies does
not carry the fold; the SDK keeps a second message identifier beside
`message_hash`; agreement between hosts holds by copying a file, not by
specification; and roles are unreachable because the artefact that carries
them is not the one that carries state.

### What this specification does

It adopts the deployed algebra unchanged in substance, states it as a kernel
with sugar, makes it a dialect clause with an installation check, moves the
fold and the binder into `cbcl-core`, and closes the four gaps. It corrects
one claim in cbcl-aamas §6.2: the per-signer and per-key selectors do not
order by causal depth. Under R5 acyclicity a same-verb group never contains
a member's predecessor, so the depth the interpreter computes over that
group is identically zero; the deployed order is the content address.

## Requirements

Each requirement points at the Reference for its definition; the Reference
is normative, the requirement fixes the obligation and its trace.

### Clause and carrier

**REQ-1900: State clause.** The dialect parser SHALL accept an OPTIONAL
`(state …)` clause and an OPTIONAL `(:state-bounds …)` clause per R.1, at
most one of each. Trace: [[SPEC-019-state-rules#TEST-1900]], [[SPEC-019-state-rules#CON-1900]].

**REQ-1901: Closed vocabulary.** The rule heads are exactly the fourteen
of R.1 plus `domain`; any other head is a parse violation. The vocabulary
changes only with a new version of this document and of the corpus.
Trace: [[SPEC-019-state-rules#TEST-1901]].

**REQ-1902: State data on dialect types.** `Dialect` SHALL carry
`state: Option<StateClause>` and `state_bounds: StateBounds`, so that
`r7_violations`, `fold`, and `intend` are functions of the `Dialect` value.
Trace: [[SPEC-019-state-rules#TEST-1900]], [[SPEC-019-state-rules#CON-1903]].

**REQ-1903: Signature-bound.** The canonical body of a dialect
([[SPEC-014-role-layer-endpoint-projection#REQ-624]]) SHALL include both
clauses and the compiler-inserted `:replaces` shape rules, as a new
canonical-form version. Trace: [[SPEC-019-state-rules#TEST-1903]].

**REQ-1904: Bounds.** The four bounds of R.1 SHALL take their defaults when
absent and SHALL be checked at installation (a bound above its default is
a violation). Trace: [[SPEC-019-state-rules#TEST-1904]], [[SPEC-019-state-rules#ADR-1911]].

### Installation (R7)

**REQ-1905: References resolve.** Every verb a rule names SHALL be a
performative of this dialect; every key SHALL be a required keyword of that
performative's shape with a type; the dialect SHALL have a protocol clause
with exactly one opener. Trace: [[SPEC-019-state-rules#TEST-1905]].

**REQ-1906: Typing.** Key fields, `set-union`/`observed-set` value fields,
and `values*` value fields SHALL be scalar (`string`, `number`, `bool`) or,
for `values`, a scalar list; `counter` names two distinct verbs carrying a
`number` field of the same name; `histogram` and `sum` name a map-valued
field defined earlier in the clause, `sum` one whose values are `number`;
no rule names a `symbol` or `keyword` field. Types follow the sugar table.
Trace: [[SPEC-019-state-rules#TEST-1906]].

**REQ-1907: `:replaces` is bookkeeping.** Installation SHALL add
`(require :replaces list)` to the shape of every writer, delete, and remove
verb of R.1 and SHALL reject a dialect that declares `:replaces` itself,
names it in a rule, or gives a delete verb any field beyond the key. One
delete verb serves one register. Trace: [[SPEC-019-state-rules#TEST-1907]], [[SPEC-019-state-rules#ADR-1901]].

**REQ-1908: Domains.** A `domain v k F` entry SHALL name a `string` key
of `v` and a list-valued field `F` whose rule names only the opener.
Trace: [[SPEC-019-state-rules#TEST-1908]], [[SPEC-019-state-rules#ADR-1909]].

**REQ-1909: Opt-in.** `r7_violations` SHALL be empty for a dialect with
neither clause. Trace: [[SPEC-019-state-rules#TEST-1909]].

**REQ-1910: Integration.** `DialectRegistry::install` SHALL run
`r7_violations` with R1–R6 and reject on a non-empty result via
`DialectInstallError::R7`; every binding's `verify_dialect` reports it.
Trace: [[SPEC-019-state-rules#TEST-1910]].

### Receipt

**REQ-1911: Closed field sets.** Per R.4, an act of a state-bearing verb
with an undeclared keyword is a shape violation. Trace: [[SPEC-019-state-rules#TEST-1911]].

**REQ-1912: Bounds on state-bearing fields.** Per R.4. Fields no rule names
are bounded only by R2 and transport. Trace: [[SPEC-019-state-rules#TEST-1912]].

**REQ-1913: `:replaces` carries addresses.** Per R.4. Trace: [[SPEC-019-state-rules#TEST-1913]].

**REQ-1914: Admission never reads history.** The R7 state-shape check
SHALL run in the shape stage, after authentication and before
`verify_causal`, and SHALL depend on the message alone. Domains are not
checked at admission ([[SPEC-019-state-rules#ADR-1909]]).
Trace: [[SPEC-019-state-rules#TEST-1914]].

### Semantics

**REQ-1915: R7.** `fold(clause, acc(t))` SHALL be total on finite sets and
SHALL depend on `acc(t)` only as a set: invariant under permutation and
duplication, independent of time, randomness, replica, and other threads.
Trace: [[SPEC-019-state-rules#TEST-1915]], [[SPEC-019-state-rules#TEST-1940]].

**REQ-1916: The order.** `pick` selects the greatest address and nothing
else; no rule consults depth, chain length, or a timestamp.
Trace: [[SPEC-019-state-rules#TEST-1916]], [[SPEC-019-state-rules#ADR-1902]].

**REQ-1917: Kernel semantics.** Each rule SHALL compute the R.2 definition
by way of the sugar table; the properties listed there SHALL hold.
Trace: [[SPEC-019-state-rules#TEST-1917]], [[SPEC-019-state-rules#TEST-1941]]–[[SPEC-019-state-rules#TEST-1944]].

**REQ-1918: Values and rendering.** Per R.3. Trace: [[SPEC-019-state-rules#TEST-1918]].

**REQ-1919: Integers.** Per R.3; no rounding rule exists.
Trace: [[SPEC-019-state-rules#TEST-1919]], [[SPEC-019-state-rules#ADR-1904]].

**REQ-1920: One address.** Per R.6. No consumer SHALL key state, `:replaces`,
or the corpus by a second identifier. Trace: [[SPEC-019-state-rules#TEST-1920]], [[SPEC-019-state-rules#ADR-1905]].

### The binder

**REQ-1921: Pure.** `intend` SHALL be a pure function of its arguments per
R.5; it never signs, sends, stores, or reads a clock.
Trace: [[SPEC-019-state-rules#TEST-1921]].

**REQ-1922: Deterministic binding.** Steps 3 and 5 of R.5 (recipient set,
role gate, predecessor) SHALL be computed exactly as written.
Trace: [[SPEC-019-state-rules#TEST-1922]].

**REQ-1923: Replacement binding.** Step 4 of R.5: the binder names up to
`max-list` current writes in address order and never rejects for having
more; a delete verb with nothing to delete rejects.
Trace: [[SPEC-019-state-rules#TEST-1923]].

**REQ-1924: Domain refusal.** Step 2 of R.5. Trace: [[SPEC-019-state-rules#TEST-1924]].

**REQ-1925: Rejection is total and silent.** Every reject carries one of
the R.5 reasons and leaves store and transport untouched.
Trace: [[SPEC-019-state-rules#TEST-1925]].

**REQ-1926: Soundness.** A returned act SHALL verify `Valid` (and
role-conformant) against `acc(t) ∪ {act}`, SHALL satisfy R.4, and its
`:replaces` SHALL equal the current writes the binder saw; two replicas
with the same `acc(t)` and intent SHALL return byte-identical text.
Trace: [[SPEC-019-state-rules#TEST-1926]], [[SPEC-019-state-rules#TEST-1946]].

### Identity, distribution, presentation

**REQ-1927: Name from hash.** Per R.6. Trace: [[SPEC-019-state-rules#TEST-1927]], [[SPEC-019-state-rules#ADR-1903]].

**REQ-1928: Teach.** Per R.6. A receiver installs through R1–R7, MAY hold
openers pending, MAY query for a definition by name, and SHALL NOT install
one from an opener's fields. Trace: [[SPEC-019-state-rules#TEST-1928]], [[SPEC-019-state-rules#ADR-1908]].

**REQ-1929: Presentation is separate.** The dialect's body, hash, and
signature SHALL NOT depend on any presentation. A presentation binds to a
dialect by its name and receives state, `may_send`, and `frontier`; it is
never given the acts, the store, or the opener. A dialect author who wants
a value displayed projects it. Trace: [[SPEC-019-state-rules#TEST-1929]], [[SPEC-019-state-rules#ADR-1907]].

### Proof, conformance, exports

**REQ-1930: Lean obligations.** `LeanCbcl/State.lean` models the accepted
set as a `List Act` under the store invariant `NodupAddr` (no two acts share
an address) with set-extensional equality `SetEq`, addresses as `Nat` (an
order-preserving image of the hex form), and collections as characteristic
functions. Proved, with only the standard axioms: `fold_perm_invariant`
(every rule of the sugar table is a set function; `pickAct_setEq` is the
order-by-address core), `fold_dedup_invariant` (the store's `insertAct`
ignores a re-delivered act); `acts_mono`, `count_mono`, `has_mono`,
`exists_mono` under store growth (`Sublist`); `mem_current_iff`,
`replaced_never_current`, `unnamed_is_current`, `registerPerKey_from_current`;
`sumField_insert` (once per address); and for the binder
`intend_pred_valid` (the predecessor is an accepted act of an admitted
type), `intend_replaces_current` (`:replaces` names exactly the current
writes of the key), `intend_supersedes` (those writes are not current once
the act is accepted), `intend_current_after` (the act itself is current).
Not modelled: scalar-list values, `histogram` over per-key maps (only
per-signer), domains beyond a `filter`, and the R5/R6 verifier itself,
which `intend_pred_valid` characterises as an admitted-type predecessor.
The Rust/Lean correspondence is checked by the corpus, not proved.
Trace: [[SPEC-019-state-rules#TEST-1940]]–[[SPEC-019-state-rules#TEST-1946]].

**REQ-1931: One corpus.** The corpus of cbcl-bus SPEC-085 CON-005, amended
per [[SPEC-019-state-rules#CON-1904]], SHALL be the oracle. cbcl-rs
SHALL ship a runner feeding each vector forward, reversed, and duplicated,
and SHALL pass every vector at the pinned version. Every *independent*
implementation (one that computes the fold or the binding without calling
the core) pins the vectors by content hash and passes them; a consumer that
obtains every judgement from the exports inherits conformance.
Trace: [[SPEC-019-state-rules#TEST-1931]].

**REQ-1932: Exports.** Per R.7, through `cbcl-wasm`, `cbcl-erl`, and
`cbcl-ffi` under [[SPEC-010-binding-conformance|SPEC-010]]. The frames are
one implementation, `cbcl_parser::state_exports`; a binding adds term
translation and crash containment and no semantics, so the corpus test on
the shared frames is the conformance gate for all three
([[SPEC-009-erlang-binding#CON-003]] for the NIFs).
Trace: [[SPEC-019-state-rules#TEST-1932]].

## Non-Functional Requirements

**NFR-1900:** `fold` runs in `O(F · n log n)` for `F` fields and `n` acts;
incremental recomputation is out of scope.
**NFR-1901:** `state.rs`, `r7.rs`, `intend.rs` are `no_std + alloc` and
`#![forbid(unsafe_code)]`.
**NFR-1902:** the exports produce byte-identical JSON and canonical text on
wasm32, aarch64, and x86_64 for every vector.

## Architecture Decisions

### ADR-1900: A kernel with sugar, not fourteen primitives
Fourteen author-facing names were each a commutativity proof owed forever.
They are compositions of two selections (`acts`, `current`) and five
reductions; `observed-set` turned out to be `current` keyed by value. The
names stay for authors and are defined by the table in R.2; proofs and
typing live on the kernel. Rejected: author-supplied code (unverifiable),
a per-verb CRDT schema (cannot express one verb feeding many fields).

### ADR-1901: One reserved field, inserted by the compiler
R5 acyclicity forbids a write from naming an earlier write of its own verb
as predecessor, so supersession rides data: a list of addresses the host
fills. Registers and removals both reduce to `current`, so both use one
reserved keyword, `:replaces`, and the compiler adds it to the shapes the
clause implies. Authors never write bookkeeping the machine can write; a
caller who supplies it is forging.

### ADR-1902: One total order, the content address
The interpreter's depth-then-hash order is identically hash order on every
input R5 admits (a same-verb group never contains a member's predecessor).
Specify the address order only; parity is exact and cbcl-aamas §6.2 is
corrected. The order converges and is not fair; contested decisions are a
role's grant in the protocol, so `authorityLast` is not adopted.

### ADR-1903: Identity is the hash of the body
`dialect_hash` excludes name, signature, and hash; a state-bearing
dialect's name is derived from the hash, not hashed. A name is a pointer;
we do not hash the pointer. Every existing object type changes identity at
migration, which cbcl-aamas §8.1 already accepts.

### ADR-1904: Integers
CBCL numbers are `i64`; state-bearing numbers are integers of magnitude ≤
`max-number`; totals are exact. Fractions are minor units. The corpus is
integer-only; a JavaScript consumer passes it unchanged below 2^53.

### ADR-1905: One content address
`message_content_hash` serves `:caused-by`, `:replaces`, the fold, and the
corpus. Any consumer that invents a second identifier reproduces the
parity problem.

### ADR-1906: The binder is pure and in the core
Steps 3 to 5 of R.5 decide whether concurrent writers converge; every host
must compute them identically, so they are one function next to the fold.
Fan-in binding applies the single rule per required type; the corpus covers
single predecessors only (deliberate simplification, known ceiling).

### ADR-1907: Presentation is a separate package with its own specification
Presentation is untrusted author code behind an opt-in; authoring is
trusted host code that must run headless. They share nothing but the
dialect name and three exports. Rejected: presentation as a module of the
authoring package (a DOM in a headless package).

### ADR-1908: The definition travels as an R4-signed `teach`
The language already distributes dialects and already names one on every
act. Two signed messages open the first instance of a type; provenance of
the definition is the author's signature. Rejected: a definition inside the
opener (R2 bound conflict, no definition provenance).

### ADR-1909: Domains are fold filters
An opener-drawn domain was the one place admission read history. It is now
a filter in `acts v` and a refusal in the binder: an out-of-domain act is
accepted and contributes nothing, an honest caller never sends one, and
admission reads one message. Stratification has no exception.

### ADR-1910: The authoring SDK stays and consumes the core
`@cbcl/object` keeps JSON authoring, compiles it to a `(define …)`, names it
with `dialect_hash`, and calls `fold`, `intend`, `verify_state_shape`,
`verify_dialect`, `message_content_hash` for every judgement. Its
interpreter is deleted. The compile is specified beside cbcl-bus SPEC-085.

### ADR-1911: One bounds clause
Scattered constants became `(:state-bounds …)` with defaults, checked at
install like R2. Exceeding `max-list` current writes no longer rejects an
intent; the binder names what fits and the next write names the rest.

## Contracts

**CON-1900: Grammar.** R.1. Input: the SExpr AST; byte-level recognition is
`cbcl-parser`, unchanged. Output: `StateClause`, `StateBounds`, or
`R7Violation::Malformed`, fail closed. Implements REQ-1900, 1901, 1904.
Verified by TEST-1900, 1901, 1950.

**CON-1901: Kernel and sugar.** R.2. Implements REQ-1906, 1915–1917.
Verified by TEST-1915–1917, 1940–1944, 1931.

**CON-1902: Values.** R.3. Implements REQ-1918, 1919. Verified by TEST-1918, 1919.

**CON-1903: Rust API.**

```rust
// state.rs
pub struct StateClause { pub entries: Vec<Entry> }
pub enum Entry { Field(String, Rule), Domain { verb: String, key: String, field: String } }
pub enum Rule { /* the fourteen of R.1 */ }
pub struct StateBounds { pub max_string: u32, pub max_list: u32, pub max_number: i64, pub max_fields: u32 }
pub struct Act { pub address: ContentHash, pub verb: String, pub signer: AgentKey,
    pub predecessors: Vec<ContentHash>, pub fields: BTreeMap<String, SExpr> }
pub struct Instance<'a> { pub dialect: &'a Dialect, pub thread: &'a ThreadId, pub acts: &'a [Act],
    pub opener: Option<&'a Act>, pub cast: Option<Cast> }
pub fn instance_of<'a>(d: &'a Dialect, store: &'a ThreadedMessageStore, thread: &'a ThreadId) -> Result<Instance<'a>, R7Violation>;
pub fn fold(inst: &Instance) -> Vec<(String, Value)>;
pub fn render_json(state: &[(String, Value)]) -> String;
pub fn state_schema(d: &Dialect) -> Vec<(String, StateType)>;
pub fn frontier(inst: &Instance) -> Vec<ContentHash>;
// r7.rs
pub enum R7Violation { Malformed(String), UnknownVerb(String), UnknownField{verb,field}, Typing(String),
    Replaces(String), Domain(String), Bounds(String), Name{expected,found} }
pub fn r7_violations(d: &Dialect) -> Vec<R7Violation>;
pub fn verify_state_shape(d: &Dialect, msg: &Message) -> Result<(), ShapeViolation>;
// intend.rs
pub enum Reject { UnknownVerb, Opener, Forge(String), Role(String), Domain(String), NothingToDelete,
    NoPredecessor, Shape(ShapeViolation), NotValid(VerificationResult) }
pub fn intend(inst: &Instance, signer: &AgentKey, verb: &str, fields: BTreeMap<String, SExpr>) -> Result<Message, Reject>;
pub fn may_send(inst: &Instance, signer: &AgentKey) -> Vec<String>;
pub fn roles_of(cast: &Cast, signer: &AgentKey) -> Vec<String>;
// canonical.rs: dialect_body_hash excludes the name; dialect_name(d) = "sha256-" + hex
```

`Dialect` gains `state`, `state_bounds`; `DialectInstallError` gains `R7`.
Implements REQ-1902, 1910, 1921, 1932. Verified by TEST-1921, 1932.

**CON-1904: Conformance vector.** cbcl-bus SPEC-085 CON-005 with: `cids`
renamed `addresses` (`message_content_hash`); `contract` holds `(define …)`
text, `authoring` optionally a consumer's source; integers only;
`expect.state` per R.3; optional `intents: [{signer, thread, verb, fields,
expect: canonical | {reject}}]`. Location `test-vectors/state/`, plus
`VERSION`. Implements REQ-1931. Verified by TEST-1931.

**CON-1905: Errors.** Install: `R7Violation`, all reported together, none
installs partially. Receipt: `ShapeViolation` with rule ∈ {closed, size,
replaces}, sender blamed. Binder: `Reject` per R.5. Implements REQ-1910,
1914, 1925.

## Purity Boundary Map

Pure core: `state.rs` (clause + acts → state, schema, frontier), `r7.rs`
(dialect → violations; message → verdict), `intend.rs` (instance + signer +
intent → act or reject), `canonical.rs` (body hash, name). Effectful shell:
none added; consumers own authentication, store, signing, encryption,
transport, history, presentation. Boundary: `SExpr`, `Act`, `Instance` in;
`Value`, `Message`, violations, `Reject` out. Dependency: `state.rs` ←
`r7.rs` ← `intend.rs`, all on existing core modules; core never imports a
shell.

## Test Specifications

Example tests TEST-1900 … TEST-1932 pair with their REQ numbers, each with
a positive, a negative-input, and where applicable a negative-output case.
Fixtures: `dialects/checklist.cbcl`, `dialects/lunch-vote.cbcl`, a tag set,
a balance. Selected obligations:

**TEST-1907.** A dialect declaring `:replaces` in a shape, naming it in a
rule, or giving `drop` a second field fails install; the installed
checklist's `check` and `drop` shapes require `:replaces list`.

**TEST-1908/1924.** A `vote` whose `:choice` is not in the accepted opener's
`:options` is accepted, absent from `ballots` and `tally`, and refused by
`intend` with `Domain(choice)`.

**TEST-1922.** Cast owner=@aria, member={@bo,@cy}: `intend` for `check` from
@bo binds `to (@aria @bo @cy)` and `caused-by` M1; for `drop` from @bo
rejects `Role(owner)`; a role-free dialect binds `to` from the opener.

**TEST-1923.** With 70 current writes for one key, `intend` names 64 in
address order and succeeds; after acceptance, the next write names the
remaining 6; `drop` on an absent key rejects `NothingToDelete`.

**TEST-1927.** Renaming a dialect to `sha256-<body hash>` installs;
any other name for a state-bearing dialect is rejected before R1; changing
one rule changes the name.

**TEST-1931.** The runner passes every vector forward, reversed, duplicated;
a vector from a live session of two independent consumers is included;
mutating `pick` to the least address turns a vector red.

Property tests (proptest, `crates/cbcl-core/tests/state_properties.rs`; the pure core is the executable twin of the model, and each test names the State.lean theorem it mirrors):
**TEST-1940** permutation and duplication invariance of `fold`;
**TEST-1941** monotonicity of `acts`, `size`, `distinct`, `events`;
**TEST-1942** `mem_current_iff`; **TEST-1943** a replaced write is never
picked and a write nobody names is always current; **TEST-1944** `sum`
changes by exactly one act's amount per new address and by zero per
duplicate; **TEST-1945** (migration, retired with `projection.js`) address
order equals the interpreter's depth-then-hash on every R5-acyclic input;
**TEST-1946** `intend_sound`: the result verifies against `acc ∪ {result}`
and re-binding names it. **TEST-1950** fuzz: clause parser round-trip and
no-panic; `fold` and `intend` on random accepted sets, no-panic.

## Migration

Phase 1 (cbcl-rs): implement CON-1900–1905; land the corpus runner with
vectors transcribed from the first consumer's tests. Phase 2 (cbcl-bus):
move presentation out of `@cbcl/object` into its own package and
specification; the authoring compile emits both clauses, names by
`dialect_hash`, distributes as `teach`; `read`/`act`/`checkShape` call the
exports; `projection.js`, `emit.js`, and the renderer in `object-sdk.js`
are deleted after TEST-1945 passes. Existing objects change identity;
histories keyed by cid are read-only under the old runtime. Phase 2b
(hark): run the authoring package against the same wasm or call the native
core; drop the vendored interpreter. Phase 3 (Lean): discharge REQ-1930 in
order; update cbcl-aamas §6 and §7.

## Traceability

| REQ | CON | TEST | Anchor |
|-----|-----|------|--------|
| 1900–1904 | 1900 | 1900–1904, 1950 | cbcl-bus SPEC-085 CON-001 limits; AAMAS §6.2 |
| 1905–1910 | 1900, 1905 | 1905–1910 | `object-sdk.js` `expression()`; AAMAS §6.3 |
| 1911–1914 | 1905 | 1911–1914 | SDK rules "CBCL shapes cannot express" |
| 1915–1920 | 1901, 1902 | 1915–1920, 1940–1945 | cbcl-bus SPEC-019 CON-003, REQ-024/029/030; `projection.js`; Baquero 2017; Kleppmann 2018 |
| 1921–1926 | 1903, 1905 | 1921–1926, 1946 | cbcl-bus SPEC-019 CON-002; `emit.js`; AAMAS §6.4 |
| 1927–1929 | 1903 | 1927–1929 | SPEC-014 REQ-628; cbcl-bus SPEC-085 REQ-002, ADR-003; SPEC-019-bus ADR-009 |
| 1930–1932 | 1903, 1904 | 1931, 1932, 1940–1946 | `LeanCbcl/State.lean`; Gomes 2017; OpSets; SPEC-018 REQ-1806; SPEC-010 |

## Reading Paths

- **Dialect author**: Orientation → `dialects/checklist.cbcl` → R.1 → R.2 sugar table → R.4.
- **Implementer**: R.1–R.7 → CON-1903 → REQ-1905–1910 → Purity Boundary Map.
- **Consumer maintainer**: ADR-1903, 1905, 1907, 1908, 1910 → R.6, R.7 → Migration.
- **Presentation author**: R.5 → R.7 (`state_schema`, `may_send`, `frontier`) → REQ-1929.
- **Prover**: R.2 properties → REQ-1930 → TEST-1940–1946.

## Changelog

<details>
<summary>Revision history</summary>

- 0.3.5 (2026-09-27) — REQ-1932 complete: the seven exports moved into
  `cbcl_parser::state_exports` as the one implementation; `cbcl-wasm`
  delegates; `cbcl-erl` gains `fold/1` … `dialect_hash/1` (SPEC-009
  CON-003); `cbcl-ffi` gains `cbcl_fold` … `cbcl_dialect_hash` with the
  regenerated `cbcl.h`; the corpus drives the shared frames.
- 0.3.4 (2026-09-27) — Phase 3: `LeanCbcl/State.lean` discharges
  REQ-1930 (16 theorems, standard axioms only, listed in `AxiomAudit.lean`);
  REQ-1930 restated to say what the model is and what it leaves out.
- 0.3.3 (2026-09-27) — the self-address prefix is `sha256-`, the wire
  spelling of every content address; `object-` was the first consumer's
  vocabulary.
- 0.3.2 (2026-09-27) — implementation-driven corrections: under R6 the
  root is the cast-bearing `hello` and the opener follows it (SPEC-014
  REQ-611/623); wire addresses are `sha256-<hex>`; a state-bearing act is
  its keyword form, not a template expansion; only a claimed `sha256-`
  name is checked against the self-address; exports take S-expression
  frames; map keys render strings raw. Implemented in `cbcl-core`
  (`state.rs`, `r7.rs`, `intend.rs`), `cbcl-parser` (`state_parser.rs`),
  `cbcl-wasm`, `cbcl-cli`, with the corpus in `test-vectors/state/` and
  its runner.
- 0.3.1 (2026-09-27) — renamed: "state rules" replaces "transition
  combinators" in the title and file name ("projection" was rejected as
  colliding with endpoint projection); the Orientation says plainly that
  the layer is a query over a grow-only set of acts, not a replicated
  data type.
- 0.3.0 (2026-09-27) — simplification: a two-page Reference (R.1–R.7)
  is the normative core; the fourteen rules desugar to a kernel of two
  selections and five reductions (ADR-1900); `:replaces` is one reserved,
  compiler-inserted field (ADR-1901); `(:state-bounds …)` replaces
  scattered constants and over-full registers no longer reject (ADR-1911);
  `enum-of` becomes a `domain` entry filtered in the fold and refused by
  the binder, so admission never reads history (ADR-1909); identity is
  `dialect_hash` over the body with the name derived (ADR-1903);
  `bind_intent` renamed `intend`; the presentation interface reduced to
  `state_schema`, `may_send`, `frontier`, with `events` carrying the
  signer; `histogram`/`sum` reference a field instead of nesting.
  Requirements renumbered 1900–1932.
- 0.2.2 — ADR-1910 authoring SDK consumes the core; presentation separate.
- 0.2.1 — cast as explicit instance context.
- 0.2.0 — view author's interface; binder walkthrough.
- 0.1.1 — consumer-neutral wording.
- 0.1.0 — draft.
</details>
