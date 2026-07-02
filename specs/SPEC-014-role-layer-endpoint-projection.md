---
id: SPEC-014
title: Role Layer — R6 and Coordination-Free Endpoint Projection
status: implemented
version: 0.3.1
date: 2026-07-02
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-002 (structural contracts — causal protocols, R5 verifier)
  - SPEC-003 (verification lattice — three-valued result, monotonicity)
  - SPEC-005 (Lean mechanisation — R5 machine-checked development)
prior-art:
  - lean-cbcl/LeanCbcl/EPP.lean (EPP correspondence, safety level — no sorry)
  - lean-cbcl/LeanCbcl/EPPCompletion.lean (EPP correspondence, completion level)
  - lean-cbcl/LeanCbcl/Projectability.lean (Thm 1 — projectability iff local verifiability)
  - proofs/epp-correspondence/proof.tex (paper-level proofs)
  - anuna-papers/papers/2026-cbcl-endpoint-projection (the EPP paper; design source)
  - SPEC-004 (sealed-bid auction demo — first consumer of indexed roles)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-014: Role Layer — R6 and Coordination-Free Endpoint Projection

The key words MUST, MUST NOT, REQUIRED, SHALL, SHALL NOT, SHOULD, SHOULD NOT,
RECOMMENDED, MAY, and OPTIONAL in this document are to be interpreted as
described in BCP 14 (RFC 2119, RFC 8174) when, and only when, they appear in
all capitals.

## Orientation

Intent: Give CBCL dialects multiparty roles: declare who may send and receive
each performative, check the declaration at installation (R6), derive each
role's local monitor by [[endpoint-projection|endpoint projection]] as a pure
function every agent computes identically, and enforce it with the existing
R5 verifier plus a role-conformance check — no central compiler, router, or
ordered transport. This implements the "engineering that remains" of the EPP
paper, whose theorems are already mechanised in Lean.

Metaphor: the choreographer is replicated at every endpoint — each dancer
derives their own part from the same shared score, and no conductor exists.

Structure:

```
 gossiped dialect                          thread runtime
┌──────────────────┐  install   ┌─────────────────────────────────┐
│ :roles / :from / │──────────▶ │  with-roles wrapper = cast      │
│ :to annotations  │  R6 check  │  (CON-601, root convention)     │
│ (CON-600)        │ (r6.rs)    └───────────────┬─────────────────┘
└────────┬─────────┘                            │ seal cast
         │ project(P, endpoint)  — pure fn      ▼
         ▼                            ┌──────────────────────┐
┌──────────────────┐   verify per msg │ verify_causal_for_   │
│ LocalProtocol    │◀───────────────▶ │ role = role conform  │
│ per endpoint     │                  │ + R5 verify_causal   │
│ (projection.rs)  │                  │ (CON-602)            │
└──────────────────┘                  └──────────────────────┘
   arrows point inward → role layer is pure core; store access read-only
```

Decisions: [[SPEC-014-role-layer-endpoint-projection#ADR-600]] indexed-role
concrete syntax `(* name)` · [[SPEC-014-role-layer-endpoint-projection#ADR-601]]
placement in `cbcl-core` modules ·
[[SPEC-014-role-layer-endpoint-projection#ADR-602]] eager valid-is-sticky
verdict retained · [[SPEC-014-role-layer-endpoint-projection#ADR-603]] root
convention and root typing ·
[[SPEC-014-role-layer-endpoint-projection#ADR-604]] R5 runs on the
dialect-level protocol; occupants live in the role layer ·
[[SPEC-014-role-layer-endpoint-projection#ADR-605]] R6(iii) subsumed by (vi)
in v1

Load-bearing: [[SPEC-014-role-layer-endpoint-projection#REQ-604]] causal
locality (R6 vi) · [[SPEC-014-role-layer-endpoint-projection#REQ-609]]
projection determinism · [[SPEC-014-role-layer-endpoint-projection#REQ-617]]
role-local verification composes R5 ·
[[SPEC-014-role-layer-endpoint-projection#REQ-618]] occupant-counted fan-in ·
[[SPEC-014-role-layer-endpoint-projection#REQ-622]] recipient sets on
messages · [[SPEC-014-role-layer-endpoint-projection#REQ-623]] root typing

Open: same-key equivocation (one occupant emitting two conflicting decisions
for one choice instance) is not detected by per-message verification; it is a
configuration-level safety property, deferred with rationale in
[[SPEC-014-role-layer-endpoint-projection#ADR-604]] (owner: HOC) · splicing
regime (non-vacuous bystander erasure) out of scope, future spec · parser
wiring stays at the SExpr level in `cbcl-core::dialect`; `cbcl-parser` (byte
level) is unchanged except the recipient-set position of
[[SPEC-014-role-layer-endpoint-projection#REQ-622]] (owner: HOC).

Detail: requirements below; Lean model in `lean-cbcl/LeanCbcl/EPP.lean`,
`EPPCompletion.lean`, `Projectability.lean`; design rationale in the EPP
paper (anuna-papers).

## Context

[[SPEC-002-structural-contracts|SPEC-002]] gave dialects causal protocols
("X may follow Y") checked by `verify_causal` over a content-addressed store,
with the three-valued [[SPEC-003-verification-lattice|verification lattice]]
of SPEC-003. That layer is deliberately role-agnostic, which confines it to
two-party interaction. The EPP paper adds roles and shows that endpoint
projection — deriving one local monitor per role from a single global
protocol — survives the loss of the central choreographer, ordered channels,
and rational-participant assumptions, exactly when the protocol is *causally
local* (R6 clause vi). The correspondence theorems are mechanised in Lean
(`EPP.lean`, `EPPCompletion.lean`, `Projectability.lean`; no `sorry`).

This spec is the Rust realisation. The pure core mirrors the Lean model so
the mechanised theorems become executable property tests; the concrete layer
parses role annotations, runs R6 at installation, and composes role
conformance with the unchanged R5 verifier.

Scope notes, fixed by the paper's v1 and carried over verbatim:

- Recipient annotations are **sets** from the start: a bare symbol is a
  singleton, a list is a multicast, `()` is a terminal act with no recipient.
- The **root convention**: the distinguished root `begin` counts every
  declared role among its endpoint roles, and the [[role-cast|cast]]-bearing
  wrapper that opens a thread is addressed to the entire cast. Without this,
  [[causal-locality|causal locality]] fails at every first step.
- **R6 is checked at two levels**: a dialect-level installation check
  (indexed roles treated as single role names) and a cast-instantiated check
  of clause (vi) run once at thread open for dialects with indexed roles.
- The bystander splice is **vacuous** under R6(vi); the splicing regime is
  out of scope.
- Recursion is out of scope: a v1 protocol is a finite DAG, every
  conversation finite.

Terminology used below. An *endpoint* is a `(role, occupant)` pair; for a
singleton role the occupant is implicit. A performative's *endpoint roles*
are its `:from` role and every member of its `:to` set. *Occupancy and
ratification*: the cast *nominates* keys; a singleton role is *occupied*
exactly by the nominated key sending a message the projection attributes to
that role (ratification by signature); an indexed role is occupied by any
key its sealed membership admits; a *receive-only* role (one with no Send
step in its projection) is never ratified, only nominated — sound because it
bears no sending obligation; an agent *declines* by never acting. A *choice*
is any disjunctive alternative set in the protocol: the member set of a
`NodeRef::Any`, wherever it appears, and the alternative entries of a step's
predecessor list when it offers more than one alternative.

## Requirements

### Role declaration and parsing

**REQ-600: Role declaration attribute.**
The dialect parser SHALL accept an OPTIONAL `:roles` attribute on a `define`
form, positioned like the existing `:extends`/`:resources` attributes, whose
value conforms to [[SPEC-014-role-layer-endpoint-projection#CON-600]] (bare
symbol = singleton role; `(* name)` = indexed role per
[[SPEC-014-role-layer-endpoint-projection#ADR-600]]).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-600]],
[[SPEC-014-role-layer-endpoint-projection#CON-600]].

**REQ-601: Role-completeness (R6 i).**
The R6 checker SHALL reject a role-declaring dialect in which any
performative named in the causal protocol declaration lacks a `:from`
annotation or a `:to` annotation (the distinguished `begin` excepted; core
performatives not named in the protocol are unconstrained).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-601]].

**REQ-602: Undeclared-role rejection.**
The R6 checker SHALL reject a dialect in which a `:from` or `:to` annotation
names a role absent from the `:roles` declaration, or in which a `:from`/
`:to` annotation appears while no `:roles` attribute is declared (stray
annotations fail closed).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-602]].

**REQ-621: Role data on dialect types.**
`Dialect` SHALL carry the parsed role declarations
(`roles: Vec<RoleDecl>`) and `PerformativeDef` SHALL carry the parsed
annotation (`role: Option<RoleAnnotation>`), populated by the dialect
parser, so that `r6_violations` and `project` are functions of the `Dialect`
value alone.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-600]],
[[SPEC-014-role-layer-endpoint-projection#CON-602]].

**REQ-624: Role annotations are signature-bound.**
The canonical signable S-expression of a dialect (and its serialised form)
SHALL include the `:roles` attribute and every per-performative `:from`/
`:to` annotation, as a new canonical-form version, so role annotations
cannot be stripped or rewritten in gossip without invalidating the R4
signature.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-624]].

### R6 installation checks (dialect level)

**REQ-603: Chooser coherence (R6 ii).**
For every choice (see Terminology: `NodeRef::Any` member sets anywhere in
the protocol, and multi-alternative predecessor lists), the R6 checker SHALL
reject the dialect unless all members share one sender role.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-603]].

**REQ-604: Causal locality (R6 vi), type level.**
The R6 checker SHALL reject the dialect unless, for every performative `t`
and every predecessor type `t'` named in `t`'s protocol clause, every
endpoint role of `t` is also an endpoint role of `t'`, where `begin` counts
every declared role among its endpoint roles
([[SPEC-014-role-layer-endpoint-projection#ADR-603]]).
Dialect-level projectability (R6 iii) is subsumed: see
[[SPEC-014-role-layer-endpoint-projection#ADR-605]].
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-604]].

**REQ-605: Role reachability (R6 iv).**
The R6 checker SHALL reject the dialect unless every declared role is an
endpoint role of at least one performative reachable from `begin` in the
protocol graph.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-605]].

**REQ-606: Per-member choice for indexed choosers (R6 v).**
For a choice whose chooser role is indexed, role-local verification SHALL
evaluate each occupant's choice as its own per-member instance (occupant
`k`'s decision message justified by occupant `k`'s own predecessor
instance), so that the single-decider-per-decision guarantee reduces to the
cast binding: one key per singleton role
([[SPEC-014-role-layer-endpoint-projection#REQ-612]]), one instance per
occupant. Clause (v) of the paper is trivially satisfied at dialect level in
v1 (the only cardinalities are singleton and indexed); same-key equivocation
is deferred (see Open).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-606]].

**REQ-607: Opt-in checking.**
`r6_violations(&Dialect)` SHALL return an empty violation list for any
dialect that declares no `:roles` attribute and carries no `:from`/`:to`
annotations (roles are opt-in; R1–R5 remain sufficient for the deployed
core).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-607]].

**REQ-627: Installation integration.**
`DialectRegistry::install` SHALL run `r6_violations` alongside the existing
R1–R5 checks and reject installation on a non-empty result via a new
`DialectInstallError` variant carrying the violations.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-607]].

### Cast-instantiated check (thread open)

**REQ-608: Per-occupant causal locality.**
`r6_instantiated_violations(&Dialect, &Cast)` SHALL reject any cast
instantiation in which some occupant of an indexed role is an endpoint of a
message type whose per-occupant predecessor instances that occupant does not
send or receive (e.g. `declare-winner :to bidder` naming every occupant's
`reveal`, per the auction analysis), evaluating occupant copies as
`(performative, occupant)` pairs
([[SPEC-014-role-layer-endpoint-projection#ADR-604]]).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-608]].

### Projection

**REQ-609: Projection function.**
`project` SHALL be a pure function from a role-annotated dialect and an
endpoint to a local protocol in which a performative whose `:from` role is
the endpoint's role is a Send step, one whose `:to` set contains it is a
Recv step, and one in which it is no endpoint is erased without rewriting
any predecessor reference (the splice is vacuous under R6 vi).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-609]],
[[SPEC-014-role-layer-endpoint-projection#TEST-630]].

**REQ-610: Raw-edge run projection.**
Role-local verification SHALL evaluate each message against the verifier's
local store using the message's raw `:caused-by` hashes, without
constructing any rewritten predecessor view.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-610]].

### Cast binding

**REQ-611: Cast nomination wrapper.**
The role layer SHALL parse a `with-roles` wrapper conforming to
[[SPEC-014-role-layer-endpoint-projection#CON-601]] at a thread's causal
root into a `Cast` assigning each singleton role exactly one key and each
indexed role a sealed key set.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-611]].

**REQ-625: Wrapper as a typed message form.**
The message layer SHALL parse `(with-roles (…) (signed …))` as a typed
wrapper form (not a `Custom` performative), content-addressed like any
message (its hash is the canonical hash of the whole wrapper S-expression,
and is the `h₀` every first step names), carrying the inner signed message
unchanged.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-625]],
[[SPEC-014-role-layer-endpoint-projection#TEST-638]].

**REQ-612: Occupancy by nomination plus signature.**
Role conformance SHALL attribute a Send step for singleton role `r` to a
message only if the message's sender key equals the key the cast nominates
for `r` (key equality per [[SPEC-014-role-layer-endpoint-projection#CON-602]];
cryptographic validity of the signature itself is an R4-layer precondition),
so a non-nominee cannot occupy `r`.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-612]].

**REQ-613: Root uniqueness.**
Role-local verification SHALL return `Violation` for a `with-roles` wrapper
whose `:caused-by` is anything other than `begin`, or whose cast differs
from the thread's root cast supplied by the caller (binding is immutable for
the life of the thread).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-613]].

**REQ-614: Sealed indexed membership.**
Occupant-dependent checks (role conformance,
[[SPEC-014-role-layer-endpoint-projection#REQ-618]] fan-in counting,
[[SPEC-014-role-layer-endpoint-projection#REQ-608]] instantiation) SHALL
read an indexed role's membership exclusively from the thread's root cast,
so no later message can enlarge or shrink it.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-614]].

**REQ-626: Receive-only roles.**
Role conformance SHALL accept messages addressed to a nominated
receive-only role (one whose projection contains no Send step) without any
ratifying signature from that role, its occupancy being nomination alone
(see Terminology; the paper's design: nothing to consent to, inactivity is
liveness).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-626]].

### Role-local verification

**REQ-615: Role conformance.**
`verify_causal_for_role` SHALL return `Violation` for a message whose
sender key or recipient set does not match, under the cast binding, the
`:from`/`:to` roles its dialect annotates for the message's performative.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-615]].

**REQ-616: No spurious predecessors.**
For a message all of whose `:caused-by` references resolve in the store,
`verify_causal_for_role` SHALL return `Violation` if any referenced
predecessor's performative type is not named in the message's protocol
clause.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-616]].

**REQ-617: R5 composition.**
`verify_causal_for_role` SHALL return the lattice meet (in the
`VerificationResult` lattice of
[[SPEC-003-verification-lattice|SPEC-003]]) of role conformance
([[SPEC-014-role-layer-endpoint-projection#REQ-615]]) with the unchanged R5
`verify_causal` run against the dialect-level `CausalProtocol`
([[SPEC-014-role-layer-endpoint-projection#ADR-604]]; REQ-616 is discharged
by this composition for resolved messages).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-617]],
[[SPEC-014-role-layer-endpoint-projection#TEST-631]].

**REQ-622: Recipient sets on messages.**
The message grammar and `Message` type SHALL support a recipient *set* per
message (bare symbol = singleton, list = multicast, `()` = empty), with
canonical (sorted) serialisation and hashing, so multicast messages like the
widened `(login (@cli @as) …)` and terminal `declare-winner` are
representable.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-622]],
[[SPEC-014-role-layer-endpoint-projection#TEST-638]].

**REQ-623: Root typing.**
In role-local verification, a `:caused-by` hash that resolves to the
thread's root wrapper SHALL satisfy a `begin` predecessor declaration (the
composition maps the root's hash to the `begin` predecessor type before
delegating to `verify_causal`), so first steps that name `h₀` verify.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-623]],
[[SPEC-014-role-layer-endpoint-projection#TEST-639]].

**REQ-618: Occupant-counted fan-in.**
For an `(all …)` fan-in whose predecessor role is indexed,
`verify_causal_for_role` SHALL map store states to verdicts as follows:
`Unknown` while any *referenced* predecessor hash is absent from the store;
once all referenced predecessors are present, `Valid` if they include a
distinct role-conformant instance of the required performative from every
sealed occupant, and `Violation` otherwise (occupant coverage is counted
over present referenced messages' sender keys, never over types alone; the
verdict is permanent from resolution, matching
[[SPEC-014-role-layer-endpoint-projection#REQ-620]]).
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-618]],
[[SPEC-014-role-layer-endpoint-projection#TEST-639]].

**REQ-619: Vacant role is liveness.**
A message whose referenced predecessor from a nominated but never-ratified
role is absent from the store SHALL remain `Unknown` (never `Violation`)
while that predecessor is absent.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-619]].

**REQ-620: Monotonicity preserved.**
`verify_causal_for_role` SHALL be monotone in the valid-is-sticky order of
the deployed clause algebra
([[SPEC-014-role-layer-endpoint-projection#ADR-602]]): `Valid` never changes
under store growth, and once every referenced predecessor is present the
verdict is permanent.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-620]],
[[SPEC-014-role-layer-endpoint-projection#TEST-636]].

## Non-Functional Requirements

**NFR-600: Checker complexity.**
The dialect-level R6 check SHALL run in O(|P|² · |R|) for |P| protocol steps
and |R| declared roles; the cast-instantiated check SHALL meet the same
bound with |P| and |R| those of the instantiated protocol.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-637]] (operation-count
guard) plus code review.

**NFR-601: Cross-agent determinism.**
`project`, `r6_violations`, `r6_instantiated_violations`, and cast parsing
SHALL produce identical results for identical inputs on any platform
(ordered collections only — `BTreeMap`/`BTreeSet`, no iteration-order
dependence), so any two agents holding the same dialect and cast compute the
same local protocols.
Trace: [[SPEC-014-role-layer-endpoint-projection#TEST-630]].

**NFR-602: no_std parity.**
The role layer SHALL compile under the same `no_std`+`alloc` configuration
and feature flags as the rest of `cbcl-core`.
Trace: CI matrix.

**NFR-603: Zero new dependencies.**
The role layer SHALL introduce no new external crate dependencies into
`cbcl-core` (Simplicity Ladder rung 4: everything needed exists in the
crate).
Trace: `Cargo.toml` diff review.

## Architecture Decisions

**ADR-600: Indexed-role concrete syntax is `(* name)`.**
The paper's `bidder[*]` marker is presentation notation: `[` lies outside
CBCL's fixed symbol alphabet, and admitting it would change the lexical
grammar R1–R3 police. The marker is rendered as the two-element form
`(* bidder)` inside the `:roles` attribute: `*` is already a legal symbol
(`cbcl-parser` symbol alphabet), the head-position operator matches every
other CBCL form (`any`, `all`, `then`, `signed`) so the recogniser
dispatches on the head like the existing `NodeRef` parse, and the prefix
Kleene star has direct Lisp precedent (Clojure spec's `(s/* pred)`, Racket
grammar DSLs). Stays within the existing S-expression lexicon and keeps the
DCFL guarantee untouched. Rejected alternatives: `(bidder *)` (dispatch on
the second element — anomalous in the codebase); `(indexed bidder)`
(session-types jargon as surface syntax); `(all bidder)` (overloads the
`all` head across roles-attr and protocol-clause positions); `bidder*` as a
naming convention (invisible to the grammar, collides with legal symbol
names); a separate `:indexed` attribute (splits one fact across two sites).

**ADR-601: Placement — three modules in `cbcl-core`.**
`role.rs` (role/cast types and SExpr-level parsing), `r6.rs` (installation
and cast-instantiated checks, mirroring the `r5.rs` entry-point pattern),
`projection.rs` (`project`, `verify_causal_for_role`). A new crate was
rejected: the layer extends the same trust boundary and reuses
`CausalProtocol`, `VerificationResult`, and `MessageStore` directly; a crate
boundary would force those types public in new ways for no consumer that
wants them (Simplicity Ladder rung 4; Constitutional Principle 15).

**ADR-602: Eager valid-is-sticky verdict retained.**
The Lean EPP model uses resolved-first semantics (no terminal verdict while
any referenced predecessor is missing). The deployed R5 clause algebra
evaluates `(any)`/`(all)` eagerly and is machine-checked monotone in the
coarser valid-is-sticky order; the two coincide from resolution onward
(paper, Prop. mono remark). The role layer reuses the deployed algebra
unchanged — rewriting it to resolved-first would fork the verifier the paper
promises to reuse. Consequence: a *provisional* `Violation` may be
superseded by `Valid` before resolution; property tests
([[SPEC-014-role-layer-endpoint-projection#TEST-636]]) assert exactly the
valid-is-sticky contract plus permanence-from-resolution.

**ADR-603: Root convention and root typing.**
`begin` counts every declared role among its endpoint roles, and the
`with-roles` wrapper (the root's runtime carrier) is addressed to the entire
cast; the wrapper's recipient set is not parsed from syntax but *defined* as
the full declared role set. Adopted from the paper (and consistent with the
Lean model, where `recip`/`precip` are instantiation data): without it,
R6(vi) fails at every first step. The runtime counterpart is *root typing*
([[SPEC-014-role-layer-endpoint-projection#REQ-623]]): traces name the root
*by hash* (`:caused-by h₀`) while protocol clauses name `begin`, and the
deployed `verify_causal` treats `begin` as a literal keyword — so the
composition must map "hash resolving to the thread's root wrapper" to the
`begin` predecessor type, or every role-annotated protocol's first messages
would fail as `InvalidPredecessor`.

**ADR-604: R5 runs on the dialect-level protocol; occupants live in the role
layer.**
The deployed `CausalProtocol` is keyed by `String` performative names
(`NodeRef::All(BTreeSet<String>)`), so feeding it synthesised per-occupant
names (`commit@b1`) would re-enter the parser's symbol space and risk
collision with legal user symbols. Instead the R5 composition
([[SPEC-014-role-layer-endpoint-projection#REQ-617]]) always runs against
the dialect-level protocol, and everything occupant-shaped lives in the role
layer: `r6_instantiated_violations` evaluates `(performative, occupant)`
pairs internally, and the occupant-counted fan-in
([[SPEC-014-role-layer-endpoint-projection#REQ-618]]) counts *sender keys of
present referenced messages* against the sealed membership. Consequence
(recorded as Open): per-message verification cannot see same-key
equivocation — two conflicting decisions by the one legitimate chooser are
each individually conformant; detecting the pair is a configuration-level
safety check, deferred (the paper's v1 likewise locates the single-decider
guarantee in the cast binding, not in a per-message check).

**ADR-605: R6(iii) subsumed by (vi) in v1.**
The paper retains projectability (iii) as a clause separate from causal
locality (vi) because (iii) survives the future splicing regime, where it is
read against the spliced local protocol. In v1's raw-edge regime the two
coincide (paper §Well-formedness), so the checker implements one check —
(vi) — and `R6Violation` carries one variant (`NotCausallyLocal`) for both.
When a splicing spec lands, (iii) gets its own check and variant; nothing in
this spec's surface changes shape.

## Contracts

### CON-600: Role-annotation grammar

Input: the SExpr AST produced by the existing CBCL reader. The byte-level
trust boundary is `cbcl-parser`, unchanged by this contract; the grammar
below is a post-parse shape over already-recognised S-expressions, in the
style of R5's `(protocol …)` clause. Terminals are SExpr atoms: `symbol` is
one symbol token (note `@alice` is a single symbol token — `@` is a symbol
character in the existing lexer).

```
roles-attr     := ":roles" "(" role-decl+ ")"        ; at least one role
role-decl      := symbol                             ; singleton role
                | "(" "*" symbol ")"                 ; indexed role (ADR-600)

from-attr      := ":from" symbol                     ; exactly one sender role
to-attr        := ":to" recipient-set
recipient-set  := symbol                             ; singleton set (sugar)
                | "(" symbol* ")"                    ; multicast; "()" = empty
```

Pre-conditions: dialect SExpr fully parsed by the existing reader; R1–R3
already passed.
Post-conditions: `Vec<RoleDecl>` and per-performative `RoleAnnotation`
values stored on the `Dialect` per
[[SPEC-014-role-layer-endpoint-projection#REQ-621]], or a violation; no
partial results.
Error model: `R6Violation::MalformedRoles`, `::MalformedFromTo` (fail
closed; no repair of malformed annotations — LangSec principle 4; an empty
`:roles ()` is `MalformedRoles`).
Implements: [[SPEC-014-role-layer-endpoint-projection#REQ-600]],
[[SPEC-014-role-layer-endpoint-projection#REQ-621]].
Verified by: [[SPEC-014-role-layer-endpoint-projection#TEST-600]],
[[SPEC-014-role-layer-endpoint-projection#TEST-601]],
[[SPEC-014-role-layer-endpoint-projection#TEST-638]] (fuzz).

### CON-601: Cast wrapper grammar

```
with-roles     := "(" "with-roles" "(" binding+ ")" signed-form ")"
binding        := "(" role-name key+ ")"
                  ; singleton role: exactly one key (else ArityMismatch)
                  ; indexed role: one or more keys (the sealed membership)
role-name      := symbol                             ; declared in :roles
key            := symbol                             ; e.g. @alice — same
                  ; lexical form as the sender identifier carried by signed
                  ; messages; compared for equality as whole symbols
signed-form    := the existing (signed …) message form (R4)
```

Pre-conditions: wrapper is the thread's causal root (the inner message's
`:caused-by` is `begin`); every `role-name` declared in the dialect's
`:roles`.
Post-conditions: a `Cast` (singleton bindings + sealed indexed memberships);
the wrapper's recipient-role set is *defined* as the full declared role set
([[SPEC-014-role-layer-endpoint-projection#ADR-603]]); the wrapper is
content-addressed as a whole
([[SPEC-014-role-layer-endpoint-projection#REQ-625]]).
Error model: `R6Violation::MalformedCast`, `::UnknownRole`,
`::ArityMismatch`; a non-root or duplicate wrapper is a `Violation` verdict
per [[SPEC-014-role-layer-endpoint-projection#REQ-613]] (role-layer verdict,
not a new `CausalViolation` variant).
Implements: [[SPEC-014-role-layer-endpoint-projection#REQ-611]],
[[SPEC-014-role-layer-endpoint-projection#REQ-614]],
[[SPEC-014-role-layer-endpoint-projection#REQ-625]].
Verified by: [[SPEC-014-role-layer-endpoint-projection#TEST-611]],
[[SPEC-014-role-layer-endpoint-projection#TEST-613]],
[[SPEC-014-role-layer-endpoint-projection#TEST-614]],
[[SPEC-014-role-layer-endpoint-projection#TEST-625]],
[[SPEC-014-role-layer-endpoint-projection#TEST-638]] (fuzz).

### CON-602: Rust API surface

```rust
// role.rs
pub enum RoleCardinality { Singleton, Indexed }
pub struct RoleDecl { pub name: String, pub cardinality: RoleCardinality }
pub struct RoleAnnotation { pub from: String, pub to: BTreeSet<String> }
/// Key identifier as it appears in casts and signed messages (e.g. "@alice").
/// Equality is whole-symbol string equality; cryptographic validity of the
/// signature that binds a message to this identifier is an R4-layer
/// precondition, outside this contract.
pub struct AgentKey(pub String);
pub struct Cast {
    pub singleton: BTreeMap<String, AgentKey>,
    pub indexed: BTreeMap<String, BTreeSet<AgentKey>>,
}
/// (role, occupant) — occupant is None for singleton roles.
pub struct Endpoint { pub role: String, pub occupant: Option<AgentKey> }
pub fn parse_roles(dialect_sexpr: &SExpr) -> Result<Vec<RoleDecl>, R6Violation>;
pub fn parse_cast(root: &SExpr, roles: &[RoleDecl]) -> Result<Cast, R6Violation>;

// dialect.rs (extended per REQ-621)
pub struct Dialect { /* existing fields… */ pub roles: Vec<RoleDecl> }
pub struct PerformativeDef { /* existing… */ pub role: Option<RoleAnnotation> }

// r6.rs — mirrors r5.rs entry points
pub fn r6_violations(d: &Dialect) -> Vec<R6Violation>;               // dialect level
pub fn r6_instantiated_violations(d: &Dialect, cast: &Cast) -> Vec<R6Violation>;

// projection.rs
pub enum LocalStep { Send, Recv }
pub struct LocalProtocol {
    pub steps: BTreeMap<String, LocalStep>,   // performative → step kind
    // predecessor clauses inherited from the dialect-level CausalProtocol
}
pub fn project(d: &Dialect, endpoint: &Endpoint, cast: Option<&Cast>) -> LocalProtocol;
pub fn verify_causal_for_role<S: MessageStore>(
    msg: &Message, endpoint: &Endpoint, d: &Dialect, cast: &Cast,
    store: &S, thread: &ThreadId, root: &ContentHash,
) -> VerificationResult;   // meet(role-conformance, R5 verify_causal) per REQ-617
```

`root` is the content hash of the thread's `with-roles` wrapper; the caller
already holds it (it is where the cast came from). It is load-bearing for
security, not a convenience: root typing
([[SPEC-014-role-layer-endpoint-projection#REQ-623]]) maps *only* this exact
hash to `begin`, so a forged mid-thread `with-roles` wrapper cannot be
referenced-as-root to smuggle a message in as a first step, and a second
wrapper distinct from the message stored at `root` is a `Violation`
([[SPEC-014-role-layer-endpoint-projection#REQ-613]]). Occupancy is ratified
by an enclosing `signed` wrapper's key alone — never the self-asserted
`:sender` field ([[SPEC-014-role-layer-endpoint-projection#REQ-612]]).

Behaviour is invariant across calling context; all functions pure given
their arguments (store access read-only through the existing `MessageStore`
trait; the caller supplies the thread's root cast and root hash — root
discovery is a caller concern, per
[[SPEC-014-role-layer-endpoint-projection#REQ-613]]).
Implements: [[SPEC-014-role-layer-endpoint-projection#REQ-607]],
[[SPEC-014-role-layer-endpoint-projection#REQ-608]],
[[SPEC-014-role-layer-endpoint-projection#REQ-609]],
[[SPEC-014-role-layer-endpoint-projection#REQ-612]],
[[SPEC-014-role-layer-endpoint-projection#REQ-617]],
[[SPEC-014-role-layer-endpoint-projection#REQ-621]].
Verified by: [[SPEC-014-role-layer-endpoint-projection#TEST-607]] through
[[SPEC-014-role-layer-endpoint-projection#TEST-620]].

### CON-603: R6 error model

`R6Violation` SHALL be an enum with one variant per rejectable condition —
`MissingFromTo`, `UndeclaredRole`, `StrayAnnotation`, `ChooserIncoherent`,
`NotCausallyLocal { perf, pred, role }`, `UnreachableRole`,
`MalformedRoles`, `MalformedFromTo`, `MalformedCast`, `UnknownRole`,
`ArityMismatch`, `PerOccupantLocalityFailure { perf, occupant }` — each
carrying the names needed to locate the defect, `Display`-formatted like
`ProtocolViolation`. One variant per rejecting REQ so failures attribute to
a single requirement.
Implements: [[SPEC-014-role-layer-endpoint-projection#REQ-601]] through
[[SPEC-014-role-layer-endpoint-projection#REQ-608]],
[[SPEC-014-role-layer-endpoint-projection#REQ-627]].

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `role.rs`: SExpr → role/cast value types
- `r6.rs`: dialect + cast → violation lists
- `projection.rs`: dialect + endpoint + cast → `LocalProtocol`;
  message + dialect + cast + store snapshot → `VerificationResult`

### Effectful Shell (orchestrates I/O, calls pure core)
- None added. Callers (agent runtime, `cbcl-cli`) own store mutation,
  transport, and root discovery; the role layer only reads through
  `MessageStore`.

### Boundary Contracts
- `SExpr` (in), `R6Violation`/`LocalProtocol`/`VerificationResult` (out)

### Dependency Rule
`role.rs` ← `r6.rs` ← `projection.rs`; all three depend only on existing
`cbcl-core` modules (`sexpr`, `dialect`, `protocol`, `store`, `message`,
`canonical`). Core MUST NOT import from CLI/WASM/FFI shells.

### Enforcement
Module visibility + code review; no new `pub use` from shell crates.

## Test Specifications

Example-based tests TEST-600 … TEST-627 pair one-to-one with their REQ
numbers; each SHALL include the positive case, the negative-input case
(precondition rejects), and — where the REQ constrains outputs — the
negative-output case, per the requirement-targeted decomposition. Worked
fixtures come from the paper: the OAuth fragment (fails R6 vi as written;
repaired by recipient widening) and the sealed-bid auction of
[[SPEC-004-sealed-bid-auction-demo|SPEC-004]] (indexed `bidder`, sealed
cast, occupant-counted fan-in, `declare-winner :to ()`).

Property tests (proptest, mirroring the Lean theorems over random
configurations; the pure core doubles as the executable twin of the Lean
model):

**TEST-630: Projection determinism.**
∀ dialect, endpoint, cast: two independent `project` calls yield equal
`LocalProtocol`s; serialisation roundtrip stable.
(Paper, Prop. Determinism — paper-only; no Lean anchor.)

**TEST-631: EPP soundness.**
∀ generated P-safe closed configuration C, endpoint r: every message of
`project(C, r)` verifies non-`Violation` against the local store.
(Lean: `soundness_safety`, `EPP.lean`.)

**TEST-632: EPP completeness.**
∀ compatible family {L_r} of locally safe runs: the glued store is safe and
closed. (Lean: `completeness_safety`, `EPP.lean`.)

**TEST-633: Exactness round-trip.**
`glue ∘ project = id` on safe closed configurations and
`project ∘ glue = id` on compatible families.
(Lean: `glue_project_eq`, `project_glue_eq`, `EPP.lean`.)

**TEST-634: Unknown means not-yet-arrived.**
∀ causally local P, partial local store L ⊆ project(C, r): an `Unknown`
verdict on an r-relevant message names a missing predecessor that is itself
r-relevant. (Lean: `unknown_means_not_yet_arrived`, `Projectability.lean`.)

**TEST-635: Converse witness.**
The straight-line counterexample (`x : A → B`, `y : C → B`,
`(then begin x y)`) is rejected by `r6_violations`, and — bypassing R6 — the
verdict of `y` at role C is `Unknown` in every reachable local store.
(Lean: `causal_locality_necessary`, `Projectability.lean`.)

**TEST-636: Monotonicity.**
∀ store S ⊆ S′: `Valid` at S implies `Valid` at S′; and once all referenced
predecessors are present at S, the verdict at S equals the verdict at S′.
(Lean: `valid_stable` for the first clause; the deployed valid-is-sticky
order per [[SPEC-014-role-layer-endpoint-projection#ADR-602]] — the
resolved-first `violation_stable` is deliberately *not* asserted before
resolution.)

**TEST-637: Checker operation-count guard.**
A debug-instrumented counter asserts the R6 checker performs
≤ c·|P|²·|R| atomic lookups over generated protocols of
|P| ∈ {10, 100, 1000} steps (falsifiable structural bound, not wall-clock).

**TEST-638: Fuzzing.**
`parse_roles`, `parse_cast`, and the recipient-set message-grammar extension
fuzzed via the existing `fuzz/` harness over arbitrary SExpr trees: no
panics, no accepted input outside CON-600/CON-601.

**TEST-639: Auction end-to-end.**
The SPEC-004 auction trace (h₀ … h₇) verifies end-to-end: every
commit/reveal `Valid` on arrival of its referenced predecessor (root typing,
[[SPEC-014-role-layer-endpoint-projection#REQ-623]]), the fan-in `Unknown`
until all three sealed reveals present then `Valid`, a four-reveal variant
with a non-member key `Violation`,
`project(C, bidder@b1) = {h₀, h₁, h₄}`, and gluing the four local runs
reconstructs the global trace.

## Traceability

| REQ | CON | TEST | Anchor |
|-----|-----|------|--------|
| REQ-600–602, 621, 624 | CON-600, CON-602, CON-603 | TEST-600–602, 624, 638 | Lean `Proto.psender`/`precip` are data; annotations are the Rust carrier |
| REQ-603, 605–607, 627 | CON-602, CON-603 | TEST-603, 605–607 | paper Def. R6 (clauses ii, iv, v — unmechanised) |
| REQ-604 | CON-603 | TEST-604, 635 | Lean `Proto.causalLocal` (vi); `Projectability.lean` both directions |
| REQ-608 | CON-602 | TEST-608 | paper §auction (per-occupant instantiation footnote; beyond mechanised model) |
| REQ-609–610 | CON-602 | TEST-609–610, 630 | Lean `project` (raw edges); determinism paper-only |
| REQ-611–614, 625–626 | CON-601 | TEST-611–614, 625–626 | paper §binding (cast is model data in Lean, not a theorem) |
| REQ-615–617, 622–623 | CON-602 | TEST-615–617, 622–623, 631–633 | Lean `conformant`, `noSpurious`, `good` |
| REQ-618 | CON-602 | TEST-618, 639 | paper §binding/auction (extension beyond the mechanised model) |
| REQ-619–620 | CON-602 | TEST-619–620, 634, 636 | Lean `isUnknown`, `valid_stable`; deployed order ADR-602 |

Intent anchors: the EPP paper (design source, not implementation oracle);
[[SPEC-004-sealed-bid-auction-demo|SPEC-004]]'s open question "where does
the auctioneer role come from?"; [[SPEC-002-structural-contracts|SPEC-002]]'s
two-party limitation.

## Changelog

- 0.3.1 (2026-07-02) — checklist-audit closes. TEST-637 (NFR-600
  operation-count guard) is now implemented over hub protocols of
  |P| ∈ {10, 100, 1000}, backed by an `ops`-tallying `r6_violations_counted`;
  `reachable_from_begin` rewritten as a worklist BFS (O(|P|+|edges|)) so the
  guard is meaningful. TEST-621 added as an explicit labelled test. The role
  layer's three modules (`role`, `r6`, `projection`) added to the
  mutation-testing scope (`mutants.toml`, `scripts/run-mutation-tests.sh`)
  with a `.forgejo` CI workflow enforcing the 90% kill-rate gate the USDD
  protocol mandates for AI-synthesised specs.
- 0.3.0 (2026-07-02) — implemented (Phase 3). Adversarial code review
  (2 High, confirmed) drove two hardening changes now reflected in CON-602:
  occupancy is ratified only by an enclosing `signed` wrapper's key, never
  the unauthenticated `:sender` field (REQ-612); and `verify_causal_for_role`
  takes the thread's `root` content hash so root typing is scoped to the
  genuine root (REQ-623) and a forged/duplicate `with-roles` wrapper is a
  Violation (REQ-613). Also: `reachable_from_begin` reduced to the NFR-600
  bound; occupant fan-in defers a non-`Multiple` reference to R5 rather than
  mislabelling it; the dialect parser fails closed on unknown `extend`
  keywords (CON-600). Status → implemented.
- 0.2.1 (2026-07-02) — stakeholder review: indexed-role marker changed from
  `(name *)` to head-position `(* name)` (ADR-600 rewritten with the
  head-dispatch rationale and widened rejected-alternatives list).
- 0.2.0 (2026-07-02) — adversarial review pass 1: role data threaded onto
  `Dialect`/`PerformativeDef` (REQ-621), recipient sets on messages
  (REQ-622), root typing (REQ-623), signature-bound annotations (REQ-624),
  typed wrapper form (REQ-625), receive-only roles (REQ-626), installation
  integration split out (REQ-627); REQ-606 rewritten (per-member choice;
  clause v trivially satisfied at dialect level in v1); REQ-618 verdict
  mapping aligned with valid-is-sticky monotonicity; REQ-613/614 rescoped to
  implementable checks; chooser-coherence scope widened to all disjunctive
  alternative sets; grammars restated over SExpr tokens; `AgentKey`
  defined with R4 precondition; ADR-604 extended (R5 on dialect-level
  protocol; equivocation deferral); ADR-605 added (iii ⊆ vi in v1); Lean
  anchors corrected.
- 0.1.0 (2026-07-02) — initial draft.
