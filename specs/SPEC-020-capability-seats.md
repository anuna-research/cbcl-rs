---
id: SPEC-020
title: Capability Seats — Delegable Authority for Role-Based Endpoint Projection
status: draft
version: 0.7.0
date: 2026-10-18
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-014 (role layer — R6, endpoint projection, cast binding)
  - SPEC-002 (structural contracts — causal protocols, R5 verifier)
  - SPEC-003 (verification lattice — three-valued result, monotonicity)
refines:
  - SPEC-014 REQ-608, REQ-612, REQ-614, REQ-615, REQ-617, REQ-618, REQ-619, and the immutable-binding clause of REQ-613
prior-art:
  - elephant theory cap-epp-lit (52 sources, 127 findings, 13 adopted options; evidence digest in Appendix A)
  - specs/SPEC-014-role-layer-endpoint-projection.md
  - lean-cbcl/LeanCbcl/Seats.lean (warrant-state model, safety level)
repository: https://codeberg.org/anuna/cbcl-rs
---

# SPEC-020: Capability Seats — Delegable Authority for Role-Based Endpoint Projection

> The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
> "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
> "OPTIONAL" in this document are to be interpreted as described in BCP 14
> (RFC 2119 and RFC 8174) when, and only when, they appear in all capitals,
> as shown here.

## Orientation

Intent: Let the people and agents in a thread change during its life. A
holder can pass on, narrow, hand over or give up its authority, and every
replica reaches the same verdict on every message from the message and its
past alone. No orderer, clock or sequencer takes part. Roles stay the unit
of [[endpoint-projection|endpoint projection]]. A role binding is a
[[capability-seat|seat]] that outlives its holders. The authority to act in
a seat is a [[warrant|warrant]], a [[object-capability|capability]] that
signed meta acts issue, narrow and remove.

Metaphor: the score stays fixed, and the chairs in the orchestra change
hands. Each player shows the signed warrant that put them in their chair.
Nobody keeps a minute-book. A player who leaves empties the chair. When two
warrants for one chair clash, the chair stays disputed until someone above
hands out a new one.

Structure:

```
 dialect (installed, pinned)                 thread log (signed DAG)
┌────────────────────────────┐             ┌─────────────────────────────────┐
│ :roles + policy clauses    │             │ with-roles root cast (+ :fixed) │
│ (CON-2000) install checks  │             │ grant/accept/revoke/resign/     │
│ projection per ROLE        │             │ reseat meta acts (CON-2001)     │
│ (SPEC-014 project, as-is)  │             └───────────────┬─────────────────┘
└─────────────┬──────────────┘                             │ in-thread authority links
              │                                            ▼
              │                       ┌─────────────────────────────────────┐
              │                       │ warrant_state over a set (REQ-2017) │
              │                       │ round membership (REQ-2046)         │
              │                       └───────────────┬─────────────────────┘
              ▼                                       ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ verify_with_capabilities (CON-2002) → one admission verdict + typed reason│
└──────────────────────────────────────────────────────────────────────────┘
   arrows point inward → pure core; store access read-only; no participant
   other than the signers takes part in any verdict
```

Terms used below (full definitions in Terminology):

- **Act**: a message of a dialect performative. **Meta act**: one of
  `grant`, `accept`, `revoke`, `resign`, `reseat`.
- **Singleton role**: one occupant. **Indexed role**: any number of
  occupants, as in SPEC-014.
- **Seat**: one role binding, such as "commander, as first given to @dana".
  Root seats come from the cast; `share` and `appoint` grants create more. A
  seat persists; the key holding it changes.
- **Warrant**: a key's signed authority to send some acts of one role. Each
  warrant belongs to a seat. A proxy is a warrant inside its delegator's
  seat: its acts count as the delegator's seat. Both words keep their
  everyday sense: the seat is the chair, the warrant is the paper that fills
  it (ADR-2016).
- **Modes of grant**: `proxy` lets a key send listed acts in the delegator's
  seat. `share` adds a co-occupant of an indexed role. `transfer` passes the
  holder's warrant to one named key once that key accepts; the seat stays. `appoint` adds an occupant to
  another indexed role that the dialect allows. `proxy`, `share` and
  `appoint` take effect at the grant; only `transfer` waits for an accept.
- **Policy-free role**: a role with no policy clause. No meta act names it.
  **Dynamic role**: a role whose seats can be created after the root,
  because it allows `share` or some role appoints into it. Any other role has
  only its root seats, whether or not it allows `transfer` or `proxy`.
- **Authority past `A(m)`**: every in-thread message reachable from `m`
  through its `:caused-by`, `:warrant`, `:seen`, `:anchor` and meta-act links.
- **`:warrant`**: the field by which an act names the warrant it relies on.
- **Concurrent**: two messages, neither in the other's authority past.
- **Counted fan-in**: an `(all …)` protocol step over an indexed role. It is
  `Valid` only when every counted seat has supplied its act or has been
  emptied.
- **Removal**: a meta act that terminates a warrant: accept, resign, revoke or
  reseat. "Admitted" means an admission verdict of `Valid`.
- **[[round-anchor|Round anchor]]**: the message a counted fan-in names with
  `:anchor`; each counted act walks back to it through its own seat's
  acts. **Round membership**: the seats of the counted role that exist in
  the anchor's authority past and are not emptied there.
- **R5**: the existing protocol-order check of SPEC-002.

Two readings of one state. The state is one relation over key, role and
act set, with a parent link. Read by role, it answers "who holds
`responder`": the live seats of the role and their holders, which is the
SPEC-014 cast extended over time. Read by key, it answers "what can @ivy
send": @ivy's live warrants and their act sets. A client fills in
`:warrant`, `:seen` and `:anchor` itself, so a user never types a warrant.

| Plain request | Meta act | Effect on the state |
|---|---|---|
| add @ivy as a responder | `share` | a new seat in `responder`, with a warrant held by @ivy |
| hand my seat to @ivy | `transfer`, then @ivy's `accept` | a `Moved` warrant held by @ivy replaces mine; the seat persists |
| let the bot file findings for me | `proxy` | a narrowed warrant in my own seat, held by the bot |
| remove @ivy | `revoke` | @ivy's warrant and everything under it are removed; the seat empties |
| step down | `resign` | the same, by the holder |
| put `commander` back in safe hands | `reseat` by the recovery role | a `Reseated` warrant replaces the terminal one |

A policy-free role has only the role reading, unchanged from SPEC-014. Two
states have no role reading, and a client has to show them: a *contested*
seat, and a removal that a sender left out of its past (ADR-2011).

How a verdict is reached:

- **Warrant state.** One pure function turns a *set* of admitted meta acts into
  warrants. Each warrant records its terminations: accepts of transfers from it,
  its resign, a revoke of it, a reseat naming it. A warrant with any termination
  is removed, and so is every warrant under it. The seat persists. A
  single reseat puts the reseat's new key in the seat, whatever else
  terminates the warrant. Otherwise a single accept, with no resign or revoke,
  puts the acceptor in the seat. Otherwise the warrant has no successor.
  Its seat is then *emptied* if a resign or revoke terminated it, and
  *contested* if two transfers were accepted or two reseats landed.
- **Admission verdict.** SPEC-014's three-valued result, `Unknown`, `Valid` or
  `Violation`; "admitted" below means `Valid`. It is the only verdict. It
  uses the warrant state of the act's authority past. An act is admitted when
  its named warrant is live there and covers the act. A removal binds acts whose
  authority past contains it. An act that omits a removal is still admitted;
  this is the honest-sender limit, and it holds in every thread.
- **Counted fan-in.** An `(all …)` over an indexed role counts the round
  membership. A seat created after the anchor is outside the round: its
  acts are admitted, and a fan-in that cites one is `Violation`. A member
  seat with no act in the fan-in is met by the removals that emptied it,
  which the fan-in's authority past holds, usually through `:seen`. A contested member is met only by a referenced act of
  its own. The fan-in's own authority past is the round's cut: nothing
  outside it bears on the round.
- **Stolen key.** A thief who moves a warrant to itself is answered in three
  ways. The honest holder resigns, which blocks the move. For a granted
  warrant, its grantor revokes and re-grants. For a root seat, an occupant
  of the recovery role the dialect declares reseats it, which dominates every
  concurrent accept. Two concurrent reseats contest the seat; the remedy
  is a successor thread.

Decisions:
[[SPEC-020-capability-seats#ADR-2000]] roles stay the unit of projection; a
role is a named capability ·
[[SPEC-020-capability-seats#ADR-2001]] grants are messages in the signed log ·
[[SPEC-020-capability-seats#ADR-2002]] chains reduce by intersection; act
subsets; a redelegate bit instead of depth ·
[[SPEC-020-capability-seats#ADR-2003]] every granted act names its authority ·
[[SPEC-020-capability-seats#ADR-2004]] one verdict, from the authority past;
a counted fan-in's past is its round's cut ·
[[SPEC-020-capability-seats#ADR-2005]] no orderer: removals win, a single
reseat dominates, equals contest ·
[[SPEC-020-capability-seats#ADR-2006]] fan-in counts the seats present
at the round anchor ·
[[SPEC-020-capability-seats#ADR-2007]] a proxy acts in its delegator's seat;
it is delivered to, never addressed (REQ-2021) ·
[[SPEC-020-capability-seats#ADR-2008]] root seats are never revoked ·
[[SPEC-020-capability-seats#ADR-2009]] recovery by a declared higher role,
effective at admission ·
[[SPEC-020-capability-seats#ADR-2010]] send authority only ·
[[SPEC-020-capability-seats#ADR-2011]] removal binds honest senders only ·
[[SPEC-020-capability-seats#ADR-2012]] authority links outside R5, inside the
thread ·
[[SPEC-020-capability-seats#ADR-2013]] a transfer names one key; accepts
coalesce per holder ·
[[SPEC-020-capability-seats#ADR-2014]] an emptied seat counts as met ·
[[SPEC-020-capability-seats#ADR-2015]] liveness is claimed against delivery
fairness; deadlock-freedom is tested, liveness is not proved ·
[[SPEC-020-capability-seats#ADR-2016]] a seat is the chair and a warrant is the paper; everyday words, no coinage

Load-bearing:
[[SPEC-020-capability-seats#REQ-2017]] the warrant-state function ·
[[SPEC-020-capability-seats#REQ-2036]] authority links ·
[[SPEC-020-capability-seats#REQ-2009]] grants never widen ·
[[SPEC-020-capability-seats#REQ-2013]] designation by `:warrant` ·
[[SPEC-020-capability-seats#REQ-2046]] round anchor and membership ·
[[SPEC-020-capability-seats#REQ-2049]] anchored fan-in composes with R5 ·
[[SPEC-020-capability-seats#REQ-2034]] conservative extension of SPEC-014

Controls, policy and admission:
- [[SPEC-020-capability-seats#REQ-2035]] policy-bearing dialects install only when the caller opts in; the default is reject, and an observe mode exists.
- [[SPEC-020-capability-seats#REQ-2009]] a grant within one role SHALL NOT widen its parent's acts or delegation rights.
- [[SPEC-020-capability-seats#REQ-2008]] a proxy grant names its acts, all from the dialect's proxy list.
- [[SPEC-020-capability-seats#REQ-2003]] a proxy list excludes a singleton role's choice acts.
- [[SPEC-020-capability-seats#REQ-2011]] chains longer than 8 grants are rejected.
- [[SPEC-020-capability-seats#REQ-2004]] `share` and `appoint` target indexed roles only.
- [[SPEC-020-capability-seats#REQ-2005]] a dynamic role feeds a counted fan-in only through an anchored round.

Controls, removal and recovery:
- [[SPEC-020-capability-seats#REQ-2020]] a transfer moves nothing until the named recipient's `accept`, and the moved warrant carries the transfer's narrowing.
- [[SPEC-020-capability-seats#REQ-2023]] a removal of an act's warrant in its authority past makes the act `Violation`; a removal outside that past never does.
- [[SPEC-020-capability-seats#REQ-2037]] a single reseat dominates; a resign or revoke blocks every accept; equals contest.
- [[SPEC-020-capability-seats#REQ-2031]] reseat names the warrant it replaces and needs a declared, acyclic, sending recovery role.
- [[SPEC-020-capability-seats#REQ-2040]] resign and revoke need the warrant or an ancestor of it; a transfer offer is withdrawn the same way.

Controls, rounds and liveness:
- [[SPEC-020-capability-seats#REQ-2046]] a fan-in names its anchor; the anchor's performative is the one the static walk ends at; a seat created later is outside the round.
- [[SPEC-020-capability-seats#REQ-2047]] the removals that empty a member seat stand in for its act when the fan-in holds no act of it.
- [[SPEC-020-capability-seats#REQ-2048]] a grant that yields a principal warrant keeps one act in every choice group, and its seat passes the SPEC-014 locality check.
- [[SPEC-020-capability-seats#NFR-2003]] liveness claims hold under delivery fairness, and no further.

The three Controls lists together exceed the Miller cap of seven. The split
into three groups is the decomposition this version makes.

Open: threshold (k-of-n) recovery and pre-rotation (owner: HOC) · a Rust
`warrant_state` mirroring `LeanCbcl/Seats.lean` with property tests, before
implementation (owner: HOC) · Lean obligations beyond `Seats.lean`: admission
monotonicity over the full verdict, conservative extension, anchor-walk
termination (owner: HOC) · consent co-signatures on grants (owner: HOC) ·
bounded grants without an orderer, such as a proxy scoped to one round
(owner: HOC) · cross-round finality as an OPTIONAL extension for deployments
that want a sequencer; v0.5.0 holds the withdrawn design (owner: HOC) · two
concurrent reseats of one root seat contest it for good; the remedy is a
successor thread (owner: HOC) · cbcl-bus wiring: delivery of authority pasts
and to proxy holders, MLS Add/Remove from warrant events, notification before
a thread starts refusing a key (owner: cbcl-bus, spec unwritten) · a `rotate`
mode that keeps a holder's child warrants when it moves its own warrant to a new
key (owner: HOC) · balancedness as an installation check if a future grammar
adds blocking receives or recursion (owner: HOC) · the deployed REQ-608
checker's gap on the BUG-640 shape, which TEST-2053 inherits (owner: HOC) · a
vacant or contested singleton seat stalls every act that cites it; only
a reseat or a successor thread resolves it (owner: HOC) · liveness over
infinite traces in Lean, after the Rocq method (f-session-26), or by model
checking the finite fragment (f-wiki-03) (owner: HOC).

Detail: [[SPEC-020-capability-seats#Context]] (failure modes and evidence) →
[[SPEC-020-capability-seats#Requirements]] →
[[SPEC-020-capability-seats#Architecture Decisions]] →
[[SPEC-020-capability-seats#Contracts]] →
[[SPEC-020-capability-seats#Test Specifications]] →
[[SPEC-020-capability-seats#Appendix A: Literature evidence]].

## Context

### What goes wrong today

[[SPEC-014-role-layer-endpoint-projection|SPEC-014]] binds roles to keys in a
[[role-cast|cast]] carried by the thread's root `with-roles` wrapper. The
binding is immutable for the life of the thread
([[SPEC-014-role-layer-endpoint-projection#REQ-613]],
[[SPEC-014-role-layer-endpoint-projection#REQ-614]]). Six failure modes
follow. Each requirement below traces to one of them.

- **FM-1 Frozen membership.** No one can join, leave or hand over a role
  after the root. Consumers work around this in three ways, each with its own
  defect. They open a new thread and lose the context. They let a delegate
  sign with the delegator's key and lose attribution. Or they keep an access
  list in the hub that no other verifier can check.
- **FM-2 Ambient role check.** The monitor asks only "does the signer occupy
  the sender role". A key that holds authority from two sources cannot say
  which one an act uses, which is the [[confused-deputy|confused deputy]]
  (f-ocap-02, f-ocap-05). Identity checks also blame the end of a delegation
  chain and cannot revoke the responsible link (f-ocap-07, f-ocap-08).
- **FM-3 Revocation evasion by backdating.** A CBCL sender chooses its own
  causal links. A revoked holder can cite only messages from before the
  revocation, and every causal-past check admits the act (f-conv-11,
  f-conv-23, f-ocap-19). No rule over the DAG alone separates a legitimate
  concurrent act from a backdated one (f-conv-19). This spec bounds the
  damage instead of deciding the question. A counted round is cut by its
  fan-in's authority past. Nothing outside that past bears on it.
- **FM-4 Captured seat.** A stolen key can move its seat to a key the thief
  controls, and a lost key strands its seat. No message can repair either
  case today.
- **FM-5 Tie-break state resets.** Systems that settle concurrent authority
  changes with a deterministic rule over the DAG let an attacker grind or
  backdate events to win. Matrix shipped such a rule and suffered state
  resets, published as CVE-2025-49090 (f-conv-12, f-conv-14, f-conv-17,
  f-conv-18). cbcl-bus already forbids tie-breaks between concurrent MLS
  commits. This spec uses no tie-break: conflicts between equals contest the
  seat, and only a declared higher authority resolves them.
- **FM-6 Stuck round.** A seat counted by a fan-in loses its warrant by
  resign, revoke or cascade. No fan-in over that round can ever be `Valid`,
  so the thread never closes. A vacant singleton seat stalls every act
  that cites it the same way; that case stays a limit (Open). SPEC-014 names
  a vacant role as a liveness gap and bounds nothing
  ([[SPEC-014-role-layer-endpoint-projection#REQ-619]]). Session calculi
  forbid leaving before the local type ends (f-session-27), which a stolen key
  never respects.

### What the literature says

The design comes from a survey of four literatures, coordinated in the
elephant theory `cap-epp-lit`. Appendix A lists every source and finding,
and each ADR cites the findings it rests on. The main conclusions are below.

1. **Projection stays over roles.** Every sound account of dynamic
   participation projects onto roles, the classes of behaviour, and keeps
   occupancy as runtime data (f-session-01, f-session-12, f-session-16). The
   only design that makes roles first-class values gives up top-down
   projection (f-session-22). Capability work treats a role as one
   encoding of an authorisation (f-ocap-09, f-session-10).
2. **Delegation is a recorded, narrowing chain.** Certificate systems agree
   on intersection semantics: SPKI, UCAN, zcap and Meadowcap
   (f-certs-01, f-certs-09, f-certs-22, f-conv-32). They also agree that the
   prover names the path (f-certs-08, f-certs-14). Local-first systems keep
   the chain in the replicated log, because revocation needs state
   (f-conv-02, f-certs-15, f-conv-24).
3. **Grant is coordination-free; revoke is not.** Monotone operations need
   no coordination, and non-monotone ones do (f-conv-27, f-conv-26, f-conv-25).
   A grant's causal precedence over a use is provable. A revoke's precedence
   over a concurrent use is not (f-certs-28). An orderer can supply what the
   DAG cannot (f-conv-20, f-conv-21), at the price of a coordinator in every
   thread. This spec declines that price. Removal is monotone in the set of
   admitted meta acts: more information never revives a warrant. That is the
   remove-wins reading local-first systems reach when they refuse to pick a
   side (f-conv-06, f-conv-07).
4. **Social priority replaces tie-breaks.** Langshaw resolves concurrent
   attempts to bind one attribute by a declared ranking over roles, never by
   an arbitrary rule. It compiles that ranking to delegation (f-wiki-01).
   The authority tree is that ranking here: a declared recovery role
   dominates, a grantor re-grants, and equals contest. Non-liveness comes
   from too little authority or a cycle in it (f-wiki-02), which the acyclic
   recovery relation excludes.
5. **Liveness is a claim against a fairness assumption.** Mechanised MPST
   results keep safety, deadlock-freedom and liveness apart. They state
   liveness only under named fairness and for balanced protocols
   (f-session-23, f-session-24). The theorems cover processes that implement
   a subtype of their projection (f-session-25). Dynamic sessions fix the
   counted membership per block and let late joiners wait for the next one
   (f-session-28). On finite protocols the properties are decidable and can
   be model-checked without a global type (f-wiki-03, f-wiki-04). The
   admission verifier is a trace monitor. The honest-sender limit is the gap
   between what a monitor can see and what a static check can decide
   (f-wiki-05).

### Terminology

- **Act**: an instance of a dialect performative.
- **Meta act**: one of `grant`, `accept`, `revoke`, `resign`, `reseat`
  (CON-2001). Meta acts carry no protocol obligation, as SPEC-014 already
  provides for meta messages.
- **Role**: a named class of behaviour declared in `:roles`. Projection
  ranges over roles exactly as in SPEC-014. A role is *singleton* (one
  occupant) or *indexed* (any number).
- **Seat**: a root seat is one `(role, key)` binding of the root cast, named
  by its role and original key. A `share` or `appoint` grant creates a new
  seat named by the grant hash. A seat keeps its identity while its holder
  changes.
- **Warrant**: the authority to send a set of acts in one role, held by one
  key. A warrant has an id, a seat, a holder, a mode, an act set, a
  redelegate flag and a chain. Both words are everyday English (ADR-2016).
  The session-type literature says a participant occupying a role
  (f-session-01); certificate systems say an authorisation certificate
  (f-certs-01).
- **Warrant ids**:
  - `Root(seat)` for a root warrant;
  - `Grant(h)` for a `proxy`, `share` or `appoint` grant;
  - `Moved(h)` for an accepted transfer, named by the accept;
  - `Reseated(h)` for an admitted reseat.
- **Principal warrant** of a seat: the root warrant, a `share` or `appoint`
  warrant, or the `Moved` or `Reseated` warrant that replaced one of them. A proxy
  warrant is never a principal warrant.
- **Chain parent** of a warrant: for a `proxy`, `share` or `appoint` warrant, the
  warrant its grant was issued under. For a `Moved` or `Reseated` warrant, the
  chain parent of the warrant it replaces. A root warrant has none. **Chain**: the
  list of warrant ids from a root warrant down to a warrant along chain parents, with
  each replaced warrant swapped for its replacement.
- **Termination** of warrant `X`, within a set `S` of admitted meta acts, is one
  of:
  - an admitted accept of an admitted transfer grant from `X`. Accepts of one
    transfer by one key are one termination;
  - a `resign` of `X`;
  - a `revoke` of `X`;
  - a `reseat` naming `X` in `:replaces`.
- **Removal**: a meta act that terminates some warrant: accept, revoke, resign
  or reseat. **Monotone meta act**: a `proxy`, `share` or `appoint` grant.
- **Warrant attributes**: a root warrant has mode `principal` and every act of its
  role. Its redelegate flag is `#t` when its role's policy lists
  `redelegate`. A granted warrant takes the attributes its grant states, with
  mode `proxy`, `share` or `principal` (for `appoint`). A `Moved` warrant takes
  the attributes its transfer grant states and mode `principal`. A
  `Reseated` warrant copies the attributes of the warrant it replaces.
- **Delegation rights** of a warrant: a `proxy` warrant issues `proxy` grants only.
  A `share` warrant issues `share` and `proxy` grants. A `principal` warrant issues
  every mode its role's policy lists. A warrant with redelegate flag `#f` issues
  nothing.
- **Policy-free role**: a role whose declaration carries no policy clause.
  **Dynamic role**: a role that declares `share` or that an `:appoint` clause
  names.
- **Authority links** of a message: its `:caused-by`, `:warrant`, `:seen` and
  `:anchor` targets. A meta act adds its `:grant` target and hash-form
  `:replaces` target. This list is canonical; every other mention defers to it.
- **Authority past `A(m)`**: the in-thread messages reachable from `m`
  through authority links, `m` excluded.
- **Terminal warrant** of a seat, in `S`: an issued principal warrant of the
  seat with no issued successor. A seat has at most one.
- **Seat status**, in `S`: *live* when its terminal warrant is live.
  *Contested* when its terminal warrant is terminated, has no successor, and
  no resign or revoke terminated it. *Emptied* when its terminal warrant is
  removed and the seat is not contested. Cascade removal empties.
  **Discharge**: the removals in a fan-in's authority past that empty a
  member seat, standing in for its act.
- **Honest sender**: a sender whose act has, in its authority past, every
  removal it has received. The protocol cannot check this property; ADR-2011
  explains why it matters.
- **Static walk** of a counted performative, at installation: follow its
  single protocol predecessor while that predecessor is one performative of
  the counted role. It ends at the first other performative, or at the root.
  **Round anchor** of a counted fan-in: the message its `:anchor` names.
  **Anchor walk** of a counted act: follow its single protocol predecessor
  while that predecessor is an act of the same seat. The walk ends at
  the first other message.
- **Round membership**: the seats of the counted role that are root
  seats or created by a grant in `A(anchor)`. Seats emptied in
  `A(anchor)` are excluded.
- **Choice group** of a role: a maximal set of its Send performatives
  ([[SPEC-014-role-layer-endpoint-projection#CON-602]]) that are alternatives
  of one choice ([[SPEC-014-role-layer-endpoint-projection#REQ-603]]). A Send
  performative in no choice is a group by itself. The term is distinct from
  SPEC-014's Send step, which is one performative.
- **Delivery fairness**: every message of the thread eventually reaches the
  store of every recipient. It is an assumption about the environment, never
  checked by the verifier.

## Requirements

### Role policy declaration

**REQ-2000: Policy clauses on role declarations.**
For: dialect authors.
WHEN a dialect's `:roles` attribute contains a policy-bearing role
declaration per [[SPEC-020-capability-seats#CON-2000]], the dialect parser
SHALL record its policy on the role's `RoleDecl`.
Acceptance: the `RoleDecl` for each declared role carries exactly the parsed
`:delegate`, `:appoint` and `:recover-by` clauses.
Trace: [[SPEC-020-capability-seats#TEST-2000]],
[[SPEC-020-capability-seats#CON-2000]]. Failure mode: FM-1.

**REQ-2001: Policy-free is the default.**
WHEN a role declaration carries no policy clause, the system SHALL treat the
role as policy-free. No grant, accept, resign, revoke or reseat names it or
a warrant of it.
Acceptance: a dialect written for SPEC-014 parses to `RolePolicy::fixed()`
for every role. A `resign` of such a role's root warrant is rejected with
`ModeNotPermitted`.
Trace: [[SPEC-020-capability-seats#TEST-2001]]. Failure mode: FM-1
(compatibility).

**REQ-2002: Policy is signature-bound.**
The canonical signable form of a dialect SHALL include every policy clause,
as a new canonical-form version. A policy stripped or widened in transit then
invalidates the dialect's R4 signature.
Trace: [[SPEC-020-capability-seats#TEST-2002]]. Failure mode: FM-1.

**REQ-2003: Policy names declared things.**
The installation check SHALL reject a dialect in which an `:appoint` or
`:recover-by` clause names an undeclared role. It SHALL also reject a `proxy`
clause that names an act whose `:from` is not the declaring role. For a
singleton role, it SHALL reject a `proxy` clause that names an act by which
that role chooses ([[SPEC-014-role-layer-endpoint-projection#REQ-606]]).
Trace: [[SPEC-020-capability-seats#TEST-2003]]. Rationale: without this rule, a proxy holder and its delegator can make two conflicting choices as one warrant.

**REQ-2004: Sharing and appointment target indexed roles.**
The installation check SHALL reject a dialect that declares mode `share` on
a singleton role, or an `:appoint` clause that names a singleton role.
Trace: [[SPEC-020-capability-seats#TEST-2004]]. Rationale:
[[SPEC-020-capability-seats#ADR-2007]].

**REQ-2005: Dynamic roles feed fan-in only through an anchored round.**
Consider a counted `(all …)` fan-in
([[SPEC-014-role-layer-endpoint-projection#REQ-618]]) that counts a
performative of a dynamic role. The installation check SHALL run the static
walk (Terminology) for that performative. The walk SHALL end at one
performative of a singleton role, or at the root. A step meets a stop when it
reaches an `(all …)`, a multi-alternative predecessor list, or a performative
of another indexed role. WHEN that happens, the check SHALL reject the
dialect with `DynamicRoleInFanIn`. The check SHALL also reject with
`MixedRoleFanIn` an `(all …)` that counts performatives of two or more roles
when any of them is dynamic. Two counted performatives of one dynamic role
are allowed; coverage is then checked per performative (REQ-2041). The
auction's `reveal`, which follows the bidder's own `commit` after the
auctioneer's `open`, passes, and its walk ends at `open`.
Trace: [[SPEC-020-capability-seats#TEST-2005]]. Rationale:
[[SPEC-020-capability-seats#ADR-2006]].

**REQ-2038: Recovery roles form no cycle and can send.**
The installation check SHALL reject a dialect whose `:recover-by` relation
has a cycle, including a role that names itself. It SHALL also reject a
`:recover-by` role whose projection has no Send performative.
Trace: [[SPEC-020-capability-seats#TEST-2038]]. Rationale:
[[SPEC-020-capability-seats#ADR-2009]].

**REQ-2043: Meta-act names are reserved.**
The installation check SHALL reject a dialect that declares a performative
named `grant`, `accept`, `revoke`, `resign` or `reseat`. It SHALL also reject
a performative parameter named `warrant`, `seen`, `anchor` or `replaces`.
Trace: [[SPEC-020-capability-seats#TEST-2043b]].

### Cast extension

**REQ-2006: Per-thread restriction on the root.**
The `with-roles` wrapper SHALL accept an OPTIONAL `:fixed` role list per
[[SPEC-020-capability-seats#CON-2001]]. A role listed in `:fixed` is
policy-free in that thread whatever its dialect policy.
Acceptance: the parsed `Cast` carries the fixed set; a `:fixed` entry naming
an undeclared role yields `MalformedCast`. A reseat of a `:fixed` role is
rejected with `ModeNotPermitted`.
Trace: [[SPEC-020-capability-seats#TEST-2006]].

### Authority links

**REQ-2036: Authority links are outside protocol order.**
The system SHALL compute `A(m)` over authority links. R5 `verify_causal`
SHALL continue to check `:caused-by` links only. Other authority links SHALL
NOT count as protocol predecessors under
[[SPEC-014-role-layer-endpoint-projection#REQ-616]].
Acceptance: take a protocol-valid act whose `:warrant` names a grant and whose
`:seen` names a revoke. Its R5 verdict equals that of the same act without
those links.
Trace: [[SPEC-020-capability-seats#TEST-2036]]. Failure modes: FM-1, FM-3.
Rationale: [[SPEC-020-capability-seats#ADR-2012]].

**REQ-2044: Authority links stay in the thread.**
The system SHALL return `Violation` for a message with an authority link to
a message of another thread. It SHALL return `Unknown` while any authority
link target is absent from the store.
Trace: [[SPEC-020-capability-seats#TEST-2044b]]. Failure mode: FM-2.

**REQ-2042: Grantees receive the authority past.**
A consumer that delivers a grant to its holder SHALL also deliver the grant's
authority past. A consumer that admits a new warrant holder SHALL make available
every message in the authority past of the meta acts that seated it.
Trace: [[SPEC-020-capability-seats#TEST-2042b]]. Rationale: SPEC-014 causal
locality assumes an endpoint holds the predecessors it cites. A late joiner
holds none of the earlier meta acts.

### Grants and chains

**REQ-2007: Grant admission requires a held warrant.**
WHEN the system admits a `grant`, it SHALL require a live warrant named by the
grant's `:warrant`. Liveness is judged in the warrant state of `A(grant)`. The
grant's signer SHALL hold that warrant.
Trace: [[SPEC-020-capability-seats#TEST-2007]]. Failure mode: FM-2.

**REQ-2008: Grant mode and acts are permitted.**
The system SHALL reject a `proxy`, `share` or `transfer` grant whose mode or
redelegate flag the dialect policy of its role does not permit. It SHALL
reject one whose parent warrant's delegation rights (Terminology) do not
include the mode. It
SHALL reject any grant for a role that is policy-free in the thread. A
`proxy` grant SHALL carry `:acts`, and every act in it SHALL appear in the
role's `(proxy …)` list. An `appoint` grant is checked by REQ-2039 instead.
Trace: [[SPEC-020-capability-seats#TEST-2008]].

**REQ-2009: Grants within one role never widen.**
The system SHALL NOT admit a `proxy`, `share` or `transfer` grant that widens
its parent warrant. Such a grant widens its parent when either of these holds:
- its act set is not a subset of the parent's act set;
- its redelegate flag is `#t` and the parent's is `#f`.
`:acts` omitted means the parent's act set.
Trace: [[SPEC-020-capability-seats#TEST-2009]] (prohibited action),
[[SPEC-020-capability-seats#TEST-2040]] (property). Rationale:
[[SPEC-020-capability-seats#ADR-2002]].

**REQ-2039: Appointment.**
Consider an `appoint` grant into role `R` under a warrant in role `Q`. The
system SHALL admit it only if `Q` declares `:appoint (… R …)`. The warrant's
delegation rights SHALL include `appoint`. The source role's `:appoint` clause is the permission. The
target role's `:delegate` clause does not apply to the appointment itself.
The new warrant is a principal warrant of a new seat in `R`. Its act set is a
subset of `R`'s acts, all of them when `:acts` is absent. Its delegation
rights are those of a principal warrant of `R`, limited by the grant's
redelegate flag.
Acceptance: an appointment under a warrant whose role lacks the clause is
rejected with `ModeNotPermitted`. Revoking the appointer's warrant removes the
appointee. An appointee with `:redelegate #t` shares its seat onward
when `R` lists `share`, and gets `ModeNotPermitted` when it does not.
Trace: [[SPEC-020-capability-seats#TEST-2039]]. Failure mode: FM-1.

**REQ-2010: Redelegation requires the bit.**
The system SHALL reject a grant whose parent is a granted warrant issued with
`:redelegate #f`.
Trace: [[SPEC-020-capability-seats#TEST-2010]].

**REQ-2011: Bounded chain length.**
The system SHALL reject a designation that resolves through a chain of more
than 8 grants.
Trace: [[SPEC-020-capability-seats#TEST-2011]],
[[SPEC-020-capability-seats#NFR-2000]]. Rationale: zcap bounds chains for the
same reason (f-certs-21).

### Designation

**REQ-2013: Every act names a covering warrant in its own role.**
WHEN an act's authority comes from a granted, moved or reseated warrant, the act
SHALL carry `:warrant` naming that warrant's id hash. The system SHALL evaluate
the act only against the named warrant. The named warrant's role SHALL equal the
act's `:from` role in the dialect.
Acceptance:
- An act that omits `:warrant` is checked against the warrant that REQ-2015 resolves.
- An act naming a warrant that does not cover it is a `Violation`. This holds
  even when another warrant held by the signer covers the act.
- An act naming a warrant of another role is a `Violation`.
Trace: [[SPEC-020-capability-seats#TEST-2013]] (including the confused-deputy
case). Failure mode: FM-2. Rationale: [[SPEC-020-capability-seats#ADR-2003]].

**REQ-2014: Designation resolves to a warrant of this thread.**
The system SHALL return `Violation` when the hash named by `:warrant` is not an
admitted grant, accept or reseat of the same thread.
Trace: [[SPEC-020-capability-seats#TEST-2014]].

**REQ-2015: Root-warrant designation.**
The system SHALL accept `:warrant (root R K)` as a designation of the root warrant
of seat `(R, K)`. That root warrant is resolved once, in the act's authority
past, and never by a later state. WHEN the signer's key holds exactly one
root seat in `R`, the system SHALL also accept an omitted `:warrant` or
`:warrant (root R)` for that seat. WHEN it holds more than one, the system
SHALL reject both short forms.
Trace: [[SPEC-020-capability-seats#TEST-2015]]. Rationale: an ambiguous short
form re-creates the search that ADR-2003 forbids.

**REQ-2016: Signature ratifies the holder.**
The system SHALL attribute an act to a warrant only if the act's `signed`
wrapper key equals the warrant's holder key. The self-asserted `:sender` field
never decides attribution. This restates
[[SPEC-014-role-layer-endpoint-projection#REQ-612]] for every warrant.
Trace: [[SPEC-020-capability-seats#TEST-2016]].

### Warrant state

**REQ-2017: The warrant-state function.**
The system SHALL compute `warrant_state(root cast, S)` for a set `S` of
admitted meta acts as follows. The definitions are those of
`LeanCbcl/Seats.lean`; where the prose and the Lean differ, the Lean decides.
1. **Issued.** A root warrant is issued. The warrant of a `proxy`, `share` or
   `appoint` grant in `S` is issued when its chain parent is issued. The
   successor of an issued warrant (step 3) is issued. Nothing else is issued,
   so a contested warrant issues no successor at any depth.
2. **Terminations** of a warrant `X` are the admitted meta acts of `S` listed in
   Terminology.
3. **Successor.** WHEN exactly one reseat in `S` names `X`, the successor of
   `X` is that reseat's `Reseated` warrant. Otherwise, WHEN no reseat, resign or
   revoke of `X` is in `S`, exactly one accept can terminate `X`. The
   successor is then that accept's `Moved` warrant. Otherwise `X` has no successor.
4. **Removed.** A warrant is removed when `S` contains a termination of it, or
   when its chain parent is removed.
5. **Live.** A warrant is live when it is issued and not removed. A live warrant's
   chain parent is live (`Seats.live_parent`).
The result SHALL NOT depend on any order of `S`; it is a function of the set.
Removal SHALL be monotone in `S` (`Seats.removed_mono`): a larger set never
revives a warrant.
Trace: [[SPEC-020-capability-seats#TEST-2017]],
[[SPEC-020-capability-seats#TEST-2041]] (property). Failure modes: FM-1,
FM-4. Refines [[SPEC-014-role-layer-endpoint-projection#REQ-614]] and the
immutable-binding clause of
[[SPEC-014-role-layer-endpoint-projection#REQ-613]].

**REQ-2037: Dominance among terminations.**
Consider a warrant `X` with two or more terminations in `S`. The system SHALL
resolve them by REQ-2017 step 3 and nothing else:
- a single reseat issues its successor whatever else terminates `X`
  (`Seats.reseat_dominates`);
- a resign or revoke of `X` blocks every accept-based successor
  (`Seats.kill_blocks_accept`);
- two accepts issuing different warrants, or two reseats, with no resign or
  revoke, contest `X` (`Seats.two_accepts_contest`).
A contested seat stays a member of every round it belongs to. It is
resolved only by a later reseat of its terminal warrant, or by a revoke and
re-grant from an ancestor.
Trace: [[SPEC-020-capability-seats#TEST-2037]]. Failure modes: FM-4, FM-5.
Rationale: [[SPEC-020-capability-seats#ADR-2005]],
[[SPEC-020-capability-seats#ADR-2013]].

**REQ-2018: Projection is unchanged.**
The system SHALL compute each role's local protocol with SPEC-014 `project`
unchanged. A proxy warrant's Send performatives SHALL be the role's Send
performatives restricted to the proxy's act set.
Trace: [[SPEC-020-capability-seats#TEST-2018]]. Rationale:
[[SPEC-020-capability-seats#ADR-2000]].

**REQ-2019: How a root seat changes holder.**
The principal warrant of a root seat SHALL change only in three ways. They
are an accepted transfer, a `resign` by its holder, and an admitted reseat.
No `revoke` names a root warrant, because a revoke names a grant hash.
Trace: [[SPEC-020-capability-seats#TEST-2019]]. Rationale:
[[SPEC-020-capability-seats#ADR-2008]].

**REQ-2020: Transfer completes on accept and carries its narrowing.**
WHEN a grant has mode `transfer`, the system SHALL leave the parent warrant with
its issuer. The warrant moves only when an admitted `accept` by the grant's
`:to` key names the grant. The transfer grant itself is never a live warrant
and issues nothing. The `Moved` warrant takes the act set and redelegate flag
the transfer grant states, which REQ-2009 keeps within the parent's. This is
the asynchronous form of session delegation: the channel moves when the
receiver catches it, and the other party's view is unchanged (f-session-08,
f-session-09).
Acceptance:
- Before the accept, the issuer's acts under the parent warrant stay `Valid`.
- Before the accept, acts under the transfer grant are `Violation`.
- After the accept, acts under the `Moved` warrant are `Valid` and the issuer's
  acts under the parent warrant are `Violation`.
- After the accept, every warrant issued under the parent warrant is removed.
- A transfer with `:acts (report finding) :redelegate #f` yields a `Moved`
  warrant that covers neither `propose-fix` nor any further grant.
Trace: [[SPEC-020-capability-seats#TEST-2020]]. Failure mode: FM-4.

**REQ-2045: Accept admission.**
The system SHALL admit an `accept` only if all of these hold, in `A(accept)`:
- its `:grant` names an admitted `transfer` grant of the same thread;
- the accept's signer is that grant's `:to` key;
- the grant's parent warrant is live, and no revoke of the grant is present.
Two admitted accepts of one grant by one key are one termination. The
`Moved` warrant is named by the accept with the lower hash, and both accepts
designate it.
Trace: [[SPEC-020-capability-seats#TEST-2048]]. Failure mode: FM-4.
Rationale: [[SPEC-020-capability-seats#ADR-2013]].

**REQ-2040: Resign, revoke and withdrawal require authority.**
The system SHALL admit a `resign` only if its signer holds the named warrant in
the warrant state of `A(resign)`. The system SHALL admit a `revoke` of grant `G`
only if its `:warrant` names a live warrant held by its signer. That warrant SHALL
be in the chain of the warrant `G` was issued under, that warrant included. For a
`proxy`, `share` or `appoint` grant, the revoke terminates `G`'s warrant. For a
`transfer` grant, the revoke withdraws the offer. An accept whose authority
past holds the revoke is rejected (REQ-2045). An accept concurrent with
the revoke stands (REQ-2017).
Trace: [[SPEC-020-capability-seats#TEST-2046]],
[[SPEC-020-capability-seats#TEST-2033]]. Failure mode: FM-2.

**REQ-2021: Recipients and delivery follow warrants.**
The system SHALL check a message's recipient set ([[SPEC-014-role-layer-endpoint-projection#REQ-622]]) against each addressed role's warrant holders. These are the holders of live principal warrants in the warrant state of `A(m)`. A
role with no live principal warrant requires no recipient. Proxy holders are
not recipients. The delivery set of a message SHALL be its recipients plus
the holders of live proxy warrants under those recipients' warrants.
Trace: [[SPEC-020-capability-seats#TEST-2021]]. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-615]]. Limit: a sender who
cites an older authority past can omit a newer member. That costs the member
delivery, not safety; consumers deliver by their current state.

**REQ-2032: Meta acts reach everyone affected.**
The system SHALL reject a meta act whose recipient set omits any of these
keys:
- a holder of a live principal warrant in the warrant state of `A(meta act)`;
- for a grant, the grant's holder;
- for an accept, revoke, resign or reseat, the holder of every warrant it
  terminates, and the `:to` key of a reseat.
Trace: [[SPEC-020-capability-seats#TEST-2032]]. Rationale: every endpoint
needs membership changes in its authority past. This is the analogue of the
SPEC-014 root convention
([[SPEC-014-role-layer-endpoint-projection#ADR-603]]).

**REQ-2041: Fan-in counts round membership.**
For a counted `(all …)` fan-in over an indexed role, the system SHALL count
the seats in the round membership of REQ-2046, once per counted
performative. A referenced act satisfies the seat of its designated warrant
for its performative. A member seat with no referenced act for a counted
performative, and no discharge (REQ-2047), makes the fan-in `Violation` with
`MissingMember`. A referenced act of the counted performative from a
seat outside the round makes the fan-in `Violation` with
`SeatOutsideRound`, as
[[SPEC-014-role-layer-endpoint-projection#REQ-618]] treats a non-member.
Acceptance: a proxy act satisfies its delegator's seat. After a
transfer, the new holder's act satisfies the old seat. Two acts from one
seat for one performative count once.
Trace: [[SPEC-020-capability-seats#TEST-2047]]. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-618]]. Rationale:
[[SPEC-020-capability-seats#ADR-2006]].

**REQ-2046: Round anchor and membership.**
A fan-in that counts a dynamic role SHALL name its anchor with `:anchor`; one
that omits it is `Violation` with `AnchorMissing`. The anchor SHALL be an
in-thread message in the fan-in's authority past. Its performative SHALL be
the one the counted performative's static walk ends at, or the thread root
when the walk ends at the root. Otherwise the fan-in is `Violation` with
`AnchorInvalid`. This check runs whether or not the fan-in references any
counted act. For each referenced act of the counted performative, the system
SHALL run the anchor walk (Terminology). WHEN a walk ends at a message other
than the anchor, the fan-in SHALL be `Violation` with `MixedRounds`. The
round membership SHALL be computed from the warrant state over the meta acts of
`A(anchor)` (Terminology). The anchor is resolved once, from content, and
never from a later state. A fan-in over a role that is not dynamic omits
`:anchor`, and its membership is the root seats.
Acceptance: with the root as anchor, the membership equals the root
seats of the role, which is the v0.4.0 behaviour. A `close` with no
referenced report that names the root as anchor, in a protocol whose walk
ends at `request`, is `AnchorInvalid`.
Trace: [[SPEC-020-capability-seats#TEST-2051]]. Failure mode: FM-1. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-618]]. Rationale:
[[SPEC-020-capability-seats#ADR-2006]], [[SPEC-020-capability-seats#ADR-2003]].

**REQ-2047: An emptied seat counts as met.**
Consider a member seat with no referenced act of its own, for this round
and performative, in the fan-in's authority past. The system SHALL count it
as met when the seat is emptied (Terminology) in the warrant state of the
fan-in's authority past. WHEN a referenced act of that seat for this
round is present, the removals SHALL NOT stand in for it. A contested
seat is a member that only a referenced act of its own satisfies; such
an act's own authority past predates the contest. An accepted transfer
empties nothing: the successor warrant acts for the seat.
Acceptance: a fan-in that references every other seat's act and whose
authority past holds the resign is `Valid`. Without the resign, no fan-in
over that round is `Valid`. A revoke of a share's parent discharges the
share. A transfer followed by a resign of the `Moved` warrant discharges the
seat. A transfer followed by the new holder's report does not.
Limit: a collector that omits a seat's act and cites its removal is
the honest-sender limit of ADR-2011; the omitted act stays in the log.
Trace: [[SPEC-020-capability-seats#TEST-2052]],
[[SPEC-020-capability-seats#TEST-2054]]. Failure mode: FM-6. Rationale:
[[SPEC-020-capability-seats#ADR-2014]].

**REQ-2049: An anchored fan-in composes with R5.**
Consider a fan-in that carries `:anchor`. For each counted performative,
the system SHALL treat the R5 predecessor clause as satisfied exactly when
REQ-2041 and REQ-2047 hold for it. Every other clause of the fan-in's
protocol entry applies unchanged. So does
[[SPEC-014-role-layer-endpoint-projection#REQ-616]] for each `:caused-by`
entry. A fan-in whose every member is
discharged therefore carries an empty `:caused-by` for the counted
performative and is `Valid`.
Trace: [[SPEC-020-capability-seats#TEST-2056]]. Failure mode: FM-6. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-617]] and
[[SPEC-014-role-layer-endpoint-projection#REQ-618]]. Rationale: the SPEC-002
clause `(all report)` demands a `report` present, and an emptied round has
none. Without this rule REQ-2047 can never produce `Valid`.

**REQ-2048: A principal warrant can meet its projection.**
Consider a `share`, `appoint` or `transfer` grant. At admission, the system
SHALL check the grant's act set against the choice groups (Terminology) of
the granted role. The act set SHALL keep at least one performative of every
choice group. Otherwise it SHALL reject the grant with `UnliveGrant`. A
`proxy` grant is exempt, because its delegator's warrant covers the seat.
For a `share` or `appoint`, the system SHALL also run
[[SPEC-014-role-layer-endpoint-projection#REQ-608]] over the *seat cast*
of `A(grant)`. That cast's indexed entries are the live principal seats
of each indexed role, each seat as its own entry, plus the new seat.
Seats are the entries, not keys, so two seats held by one key stay
distinct and a moved seat keeps its entry. A failure is
`NotCausallyLocal`, carrying the `R6Violation`.
Trace: [[SPEC-020-capability-seats#TEST-2053]]. Failure mode: FM-6. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-608]].
Rationale: [[SPEC-020-capability-seats#ADR-2015]] (f-session-25).

### Admission verdict

**REQ-2022: Admission verdict.**
`verify_with_capabilities` SHALL return one admission verdict for every
message as a function of the message and `A(m)` only. For an act, the
verdict SHALL be the SPEC-014 role-local verdict, as refined by REQ-2049,
met with these checks against
`warrant_state(root cast, admitted meta acts of A(m))`:
- the designated warrant is live, held by the signer, of the act's role, and
  covers the act;
- the recipient set satisfies REQ-2021.
For a meta act, the verdict SHALL apply the meta act's own admission REQs.
The checks SHALL run in the order of CON-2003's table, and the first failure
names the reason (OBS-2000).
Trace: [[SPEC-020-capability-seats#TEST-2022]],
[[SPEC-020-capability-seats#TEST-2041]]. Rationale:
[[SPEC-020-capability-seats#ADR-2004]].

**REQ-2023: Removals in the authority past bind.**
Consider a termination in `A(m)` of `m`'s designated warrant or of a warrant in
its chain. WHEN the warrant has no issued successor that `m` designates, the
admission verdict SHALL be `Violation` with `WarrantNotLive`.
Trace: [[SPEC-020-capability-seats#TEST-2023]]. Failure mode: FM-3 (honest
senders). Rationale: [[SPEC-020-capability-seats#ADR-2011]].

**REQ-2024: Admission monotonicity.**
The admission verdict SHALL be monotone in the valid-is-sticky order of
[[SPEC-014-role-layer-endpoint-projection#REQ-620]]. Store growth never
changes `Valid`. The verdict is permanent once `A(m)` is present.
Trace: [[SPEC-020-capability-seats#TEST-2024]].

### Recovery

**REQ-2031: Reseat by a declared role.**
The system SHALL admit a `reseat` only if all of these hold, in the warrant
state of `A(reseat)`:
- its `:replaces` names an issued principal warrant `X` of a root seat in role
  `R`, by hash or by root designation;
- `X` is the terminal warrant of that seat;
- the dialect declares `(R … :recover-by Q)` and `R` is not `:fixed` in the
  thread;
- the signer's `:warrant` names a live principal warrant of a root seat in
  `Q` that the signer holds.
At admission the reseat is a termination of `X` (REQ-2017). When it is the
only reseat of `X` in a set, `X`'s successor is a `Reseated` warrant. That warrant
is held by the reseat's `:to` key with `X`'s attributes. A reseat of a live, contested or
emptied terminal warrant is admitted alike; that is its purpose.
Trace: [[SPEC-020-capability-seats#TEST-2031]]. Failure mode: FM-4.
Rationale: [[SPEC-020-capability-seats#ADR-2009]].

### Compatibility and enablement

**REQ-2034: Conservative extension.**
Consider a dialect with no policy. Consider a message that is not a meta
act, carries no `:warrant`, `:seen` or `:anchor`, and links only within its
thread. WHEN all hold, the system SHALL return the SPEC-014
`verify_causal_for_role` verdict as the admission verdict.
Trace: [[SPEC-020-capability-seats#TEST-2034]] (differential, the full
SPEC-014 fixture corpus). This protects SPEC-014's Lean correspondence.

**REQ-2035: Policy-bearing dialects are opt-in, with an observe mode.**
The installer SHALL reject a dialect that carries any policy clause unless
the caller passes `CapabilityPolicy::Accept` or `CapabilityPolicy::Observe`.
The default SHALL be `CapabilityPolicy::Reject`. Under `Observe`, the
verifier SHALL return the SPEC-014 verdict as the admission verdict. It
SHALL expose the SPEC-020 verdict and reason beside it, so a consumer can
compare them without refusing anyone. Under `Accept`, the SPEC-020 verdict
decides.
Acceptance: with the default, a policy-bearing dialect fails installation
with `CapViolation::CapabilitiesDisabled`. With `Observe` it installs and
every act's admission verdict equals SPEC-014's. With `Accept`, it installs
and warrants decide.
Trace: [[SPEC-020-capability-seats#TEST-2035]],
[[SPEC-020-capability-seats#TEST-2058]]. Enable path: a consumer moves from
`Reject` to `Observe` to `Accept` per dialect installation. Verdicts are
functions of content (NFR-2001), so an installed thread's verdicts never
change when the option changes. The per-thread control is `:fixed` on the
root cast, and the per-warrant control is `revoke`. Rollback of an installation
is a successor thread with a policy-free dialect. Notification of holders
before a thread starts refusing a key is the consumer's duty (Open).

## Non-Functional Requirements

**NFR-2000: Designation cost.**
Resolving one designation SHALL take O(L · log N) time. Here L ≤ 8 is the
chain length and N counts the meta acts in the authority past. The result
SHALL be cacheable per frontier.
Trace: [[SPEC-020-capability-seats#TEST-2043]] (operation-count guard).
Provisional: no measurement exists; the bound is a design target for review.

**NFR-2001: Cross-agent determinism.**
Every function in [[SPEC-020-capability-seats#CON-2002]] SHALL produce
identical results for identical inputs on any platform. Ordered collections
only, as [[SPEC-014-role-layer-endpoint-projection#NFR-601]] requires. No
function SHALL read a clock or any input outside the message and the store.
Trace: [[SPEC-020-capability-seats#TEST-2041]].

**NFR-2002: no_std parity and no new dependencies.**
The capability layer SHALL compile under the `no_std`+`alloc` configuration
of `cbcl-core` and SHALL add no external crate dependency.
Trace: CI matrix; `Cargo.toml` diff review.

**NFR-2003: Liveness under delivery fairness.**
The warrant layer SHALL satisfy two claims under delivery fairness:
- a message leaves `Unknown` once its authority past, and its anchor's
  authority past, are present. No verdict waits on a message outside those
  two sets;
- a round in which every member seat has an act or is emptied admits a
  `Valid` fan-in.
A round with a contested member admits no `Valid` fan-in until a reseat or
re-grant resolves it; that is a stated limit, not a claim. Liveness beyond
these claims is not proved. Balancedness (f-session-24) does not bear on
them: no CBCL endpoint blocks on a receive, so a role absent from a branch
waits on nothing.
Trace: [[SPEC-020-capability-seats#TEST-2054]],
[[SPEC-020-capability-seats#TEST-2055]]. Failure mode: FM-6. Rationale:
[[SPEC-020-capability-seats#ADR-2015]].

## Observability

**OBS-2000: Typed reasons.**
Every admission rejection SHALL carry exactly one `CapViolation` variant. A
rejection inherited from SPEC-014 or R5 SHALL be wrapped as
`Inherited(R6Violation)`. WHEN several checks fail, the variant is that of
the first failing row of the CON-2003 table. A consumer can count and alert
on the variants. The pure core keeps no counters.
Trace: [[SPEC-020-capability-seats#TEST-2044]].

## Architecture Decisions

**ADR-2000: Roles stay the unit of projection; a role is a named capability.**
Decision. Projection ranges over roles exactly as in SPEC-014. Authority to
act in a role is a warrant. A role is the named, addressable template from which
warrants are issued.
Evidence. Every sound dynamic-participation account projects per role and
holds occupancy as runtime data (f-session-01, f-session-12, f-session-14,
f-session-16). Capability literature treats a role as one encoding of an
authorisation (f-ocap-09). Session-type delegation transfers "the capability
of participating with a given role" (f-session-10).
Rejected. *Capabilities primary, projection over arbitrary act sets*: the
only calculus with first-class roles gives up top-down projection
(f-session-22). No published work projects over delegable capabilities.
*Roles primary with the ambient check unchanged*: an identity-based check is
confused-deputy prone (f-ocap-05, f-ocap-08).
Consequence. SPEC-014 `project` and its Lean theorems are untouched
(REQ-2018). The change concerns who acts as a role, not what a role does.

**ADR-2001: Grants are messages in the signed log.**
Decision. A grant is a signed meta act in the thread, admitted like any other
message. It is not a bearer token carried beside the log.
Evidence. Revocation needs state, which detached certificates lack
(f-conv-02). Gossiped invocation logs with proofs are the CRDT form of UCAN
(f-certs-15). Grant-before-use is provable when the grant is in the use's
causal past (f-certs-28). Sound in-session delegation keeps the delegation
inside the global protocol (f-session-18, f-session-20, f-session-21).
Rejected. *Caveat tokens* (macaroons, Biscuit): HMAC tokens verify only at
the minting service (f-certs-27), and bearer delegation defeats
access-controlled delegation channels (f-ocap-14). *Detached certificate
chains*: these force verifier-local revocation state (f-certs-19, f-certs-25),
which breaks determinism across replicas.

**ADR-2002: Chains reduce by intersection; act subsets; a redelegate bit.**
Decision. Within one role, a grant narrows its parent along two axes: act
set (subset) and redelegate flag. A warrant's delegation rights follow its mode
(`proxy` < `share` < `principal`). A boolean `:redelegate` replaces a depth
limit. An appointment starts a new role's act set. A moved warrant carries the
transfer grant's narrowing.
Evidence. Session delegation is linear: the delegator gives up the endpoint
and there is no shared use (f-session-09). `transfer` is that classical case;
`share` and `proxy` are co-occupancy, which only dynamic multirole sessions
supply (f-session-01). SPKI reduces a chain by intersecting each link's
authority (f-certs-01). It keeps the intersection syntactic so verification
needs no application semantics (f-certs-02). UCAN, zcap and Meadowcap narrow
by subset or prefix (f-certs-10, f-certs-22, f-conv-32). SPKI rejected depth
control because depth bounds neither tree width nor proxying (f-certs-03,
f-certs-04). Filtering forwarders attenuate by message kind (f-ocap-16).
Rejected. *Caveat predicates* over act arguments: they need
application-specific reduction software (f-certs-02, f-certs-11). Predicates
remain an Open extension. *Expiry bounds* (`:until`): a bound needs a clock
or a sequencer that every replica agrees on, and this spec has neither
(f-certs-12). Bounded grants return as a round-scoped proxy (Open).
Limit. A holder can always proxy for another party or mint a key it
controls (f-certs-03, f-certs-04). Narrowing therefore bounds what a warrant
authorises and who answers for it. It does not confine the holder
(f-ocap-24).

**ADR-2003: Every granted act names its authority.**
Decision. An act made under a granted, moved or reseated warrant names that
warrant's id in `:warrant`. The verifier checks the act against that warrant only
and never searches. The warrant's role has to match the act's role. A short
root form is allowed only when it names exactly one seat.
Evidence. The literature agrees on this point. Designation travels with
authority (f-ocap-01, f-ocap-03, f-ocap-04). A deputy with two authorities
has to say which one it uses (f-ocap-02). Identity lookups re-create access
lists (f-ocap-06). The prover supplies the chain (f-certs-08, f-certs-14,
f-certs-21, f-certs-23). Local-first verification cites the grant event id
(f-conv-24).
Rejected. *Ambient search* for any warrant the signer holds: seven findings
oppose it and none support it.
Consequence. Root-warrant acts of single-seat keys need no change, which
keeps SPEC-014 traces valid (REQ-2015, REQ-2034).

**ADR-2004: One verdict, from the authority past; a counted fan-in's past is
its round's cut.**
Decision. The verdict of `m` depends on `m` and `A(m)` only. There is no
second, finality verdict. The question "did this act come before or after
that removal" is not decided globally. It is decided per round. A counted
fan-in's authority past fixes which acts and which removals the round saw.
Nothing outside it bears on the round.
Evidence. Eventually consistent access control splits into an immutable
verdict from the causal past and a verdict over concurrent events
(f-conv-22, f-conv-24, f-conv-09, f-conv-10). The concurrent verdict is the
one that defeats backdating (f-conv-23), and it needs coordination
(f-conv-25, f-conv-26). Dynamic multirole sessions bound each counted block
by its unlock (f-session-02, f-session-28). The fan-in is that unlock, and it
is a message the protocol already sends. Confluent programs reach one
output whatever the delivery order (f-conv-27); `warrant_state` over a set is
confluent by construction.
Rejected. *Finality epochs from an arbiter* (v0.3.0 to v0.5.0): sound, but
every thread then depends on one key's liveness and honesty. The fold
over epochs was also the least well-defined part of three reviews. The design is
kept in v0.5.0 for a future OPTIONAL extension (Open). *Verdict on learning
of a revocation* (UCAN, Biscuit): replicas disagree until all have learned
it (f-certs-19, f-certs-25). *Strong removal over concurrent events*
(p2panda): the verdict changes as late events arrive, and a backdater steers
it (f-conv-06, f-conv-18).
Consequence. A removed holder's backdated act is admitted, stays in the log,
and counts for a round only if the collector's authority past holds it.
Consumers act on admission and treat membership as what the authority past
says it is. Owner decision 2026-10-18 (`review-round 5-decision` in the
theory).

**ADR-2005: No orderer: removals win, a single reseat dominates, equals
contest.**
Decision. Concurrent terminations of one warrant are resolved by the authority
tree and by nothing else. A resign or revoke blocks every accept. A single
reseat by the declared recovery role dominates every other termination. Two
accepts, or two reseats, contest the seat until an ancestor revokes and
re-grants, or a later reseat lands alone. No rule over the DAG picks winners,
and no participant sequences anything.
Evidence. Langshaw replaces arbitrary tie-breaks with a declared ranking of
roles over each attribute and compiles the ranking to delegation
(f-wiki-01). The `:recover-by` relation and the grant tree are that ranking.
p2panda refuses to pick a side when managers remove each other (f-conv-07).
Removal is monotone, so remove-wins needs no coordination (f-conv-26,
f-conv-27). A single-recipient transfer leaves the only symmetric case to
the same key accepting twice, which coalesces (ADR-2013).
Rejected. *Deterministic tie-breaks* (power, timestamp, hash, seniority):
gameable by grinding or backdating, and they produced Matrix state resets
(f-conv-12, f-conv-14, f-conv-17, f-conv-18). *An arbiter's explicit order*:
see ADR-2004. *Accept beats resign*: a thief who moves a stolen warrant then
beats the honest holder's resign.
Limit. A contested root seat whose recovery role is itself contested
has no remedy but a successor thread. Two concurrent reseats contest for
good (Open).

**ADR-2006: Fan-in counts the seats present at the round anchor.**
Decision. A counted `(all …)` counts the seats of its role present in
the round anchor's authority past and not emptied there. The fan-in names
its anchor, the anchor's performative is fixed at installation, and each
counted act walks back to it through its own seat's acts. A dynamic role
feeds fan-in only when that walk is single-valued at installation.
Evidence. Dynamic Multirole Session Types makes send polls and receive
polls agree by locking the registry around each block with a two-phase
commit. Late joiners wait for the next block (f-session-02, f-session-28).
The registry is one synchronous object (f-session-29). In CBCL the opener's
authority past is that lock: one content-addressed message fixes the set
for every verifier, with no barrier. Recipients are explicit in every
message (REQ-2021), so the receive poll is already written down.
Rejected. *Root seats only* (v0.4.0): sound and needless; it excluded
every shared seat from every count. *Count over `A(fan-in message)`*:
the collector controls the set. *Infer the anchor as the counted acts'
common predecessor*: undefined when each occupant cites its own earlier
act, as the auction's `reveal` does. Undefined too when every member is
discharged. *Accept any in-thread message as anchor when no act is
referenced*: a collector then names the root and shrinks the round to
the root seats. Naming the anchor follows ADR-2003. Fixing its
performative at installation closes that hole.
Consequence. A seat created after the anchor is outside the round; its
acts are admitted, and a later anchor counts it. Proxy and moved warrants act
for seats that exist already, so they count. The opener chooses its
past and can delay seeing a grant, never un-see one; that is the
honest-sender limit of ADR-2011, visible in the log. The SPEC-014
per-occupant locality check
([[SPEC-014-role-layer-endpoint-projection#REQ-608]]) runs for each new
seat at grant admission over the seat cast (REQ-2048). cbcl-bus can
refuse to relay an opener that omits a grant the hub delivered to that
sender; that is relay policy, outside this spec.

**ADR-2007: A proxy acts in its delegator's seat.**
Decision. A proxy grant lets its holder send a subset of the role's acts in
the delegator's seat. It adds no recipient and no seat. Messages addressed
to the delegator are also delivered to the proxy holder, so the holder has
the predecessors its acts cite. A proxy never covers a
singleton role's choice acts (REQ-2003).
Evidence. Internal delegation lets a deputy act as the principal while the
principal waits (f-session-19). A filtering forwarder attenuates by message
kind without creating a new principal (f-ocap-16). Message-level privilege
annotations check the role an act is sent in (f-session-15). Session
delegation abstracts a hand-over away from the other party's type, so the
counterpart sees one seat whoever acts in it (f-session-08).
Consequence. Singleton routing and seat counting are unchanged by
proxies. Delivery widens, which consumers implement (Open).

**ADR-2008: Root seats are never revoked.**
Decision. No `revoke` reaches a root seat. Its principal warrant changes
only by accepted transfer, by `resign`, or by `reseat`. To eject a root
occupant otherwise, open a successor thread with a new root cast.
Evidence. Matrix made room creators immutable with unlimited power after
mutable creators led to takeovers and resets. It replaces a rogue creator
only by upgrading to a new room (f-conv-15, f-conv-16). Redell revokes
wholesale by changing the object identifier (f-ocap-12). Miller advises
respawning from a few durable capabilities instead of repairing broken state
(f-ocap-21).
Rejected. *Revocable root warrants*: two root occupants who remove each other
recreate the duelling-admins problem (f-conv-01, f-conv-07).
Consequence. A transfer or reseat removes every warrant issued under the old
warrant, appointments included. The new holder re-issues what it wants to keep.

**ADR-2009: Recovery by a declared higher role, effective at admission.**
Decision. A dialect can declare `:recover-by Q` on role `R`, with no cycle in
that relation and with `Q` able to send. A root occupant of `Q` can then
reseat the terminal warrant of a root seat of `R` to a new key. The reseat
names the warrant it replaces, takes effect at admission, and dominates every
concurrent accept, resign or revoke of that warrant.
Evidence. A parent-team admin manages subteam roles in Keybase, and only root
owners manage owners (f-certs-30). A delegated KERI identifier recovers
through its delegator after key compromise; a non-delegated one cannot
recover (f-certs-33). KERI lets a recovery rotation supersede ordinary events
but not another rotation (f-certs-32). The acyclic `:recover-by` relation
and the single-reseat rule play the part of that ordering.
Rejected for v1. *Quorum reseat* (f-certs-07): threshold subjects need
multi-signature acts this spec does not define. *Pre-rotation* (f-certs-31)
needs a key-event log outside CBCL. Both remain Open. *No recovery*: without
it, a stolen key keeps the warrant for good. *Reseat only through an orderer*
(v0.5.0): see ADR-2004.
Consequence. Any single root occupant of `Q` can reseat `R`. Dialect authors
choose `Q` with that power in mind. A role at the top of the relation has no
recovery; its remedy is a successor thread (ADR-2008). A receive-only role
cannot be `Q`, because it never signs anything that ratifies it. Two
concurrent reseats contest (ADR-2005).

**ADR-2010: Send authority only; confidentiality stays outside CBCL.**
Decision. Warrants govern what a key can send and the addressing of sends.
Whether a key can read content is decided by the encryption group, such as
MLS in cbcl-bus, and by history policy.
Evidence. Write revocation cannot remove read access already granted. Keyhive
separates pull, read and write effects (f-conv-03). Group key agreement under
concurrency is its own protocol (f-conv-04, f-conv-05, f-conv-29).
Rejected. *One mechanism for both*: it is sound in a static type discipline
(f-session-11) but cannot remove keys already distributed.

**ADR-2011: Removal binds honest senders only.**
Decision. Every removal takes effect through the admission verdict alone. It
binds every act whose authority past contains it and no other act. This
holds in every thread.
Evidence. A causal-past check cannot stop a sender who omits the removal from
its authority past (f-conv-11, f-ocap-19). Clock-based expiry makes the
verdict depend on the verifier's clock (f-certs-12). Without a trusted
platform, a reducing message that is not delivered fails unsafe (f-ocap-18).
A trace monitor is complete only for the monitorable fragment, and the
omitted removal is outside it (f-wiki-05).
Consequence. Consumers MUST treat removal as advisory against an adversary
who controls its own authority links. What the adversary gains is bounded by
rounds (ADR-2004): a backdated act counts only in a round whose collector
cites it. The strong remedy is a successor thread.

**ADR-2012: Authority links sit outside R5 protocol order, inside the
thread.**
Decision. `:warrant`, `:seen`, `:anchor` and meta-act targets are links in the
authority past that R5 does not check. They resolve only to messages of the
same thread. A sender SHOULD list in `:seen` every removal it has received
and not yet cited.
Evidence. R5 rejects any `:caused-by` link to a performative its protocol
does not name ([[SPEC-014-role-layer-endpoint-projection#REQ-616]]), and meta
acts are not dialect performatives. A use in Keybase embeds a Merkle root
that contains the grant, separate from its content (f-certs-28). A UCAN
invocation carries its proof chain beside its arguments (f-certs-14).
Rejected. *Meta acts as protocol predecessors*: every dialect protocol then
needs clauses for meta acts, which changes R5 and the Lean model.
*Cross-thread links*: with them, a removal in one thread removes a warrant in
another.

**ADR-2013: A transfer names one key; accepts coalesce per holder.**
Decision. A transfer grant names exactly one recipient key. Accepts of one
transfer by that key are one termination, whatever their count. The only
way two accepts conflict is through two transfers of one warrant, which
contest it (ADR-2005).
Evidence. HVK session delegation hands a channel to one receiver, and the
receiver's catch completes it (f-session-08, f-session-09). Retried accepts
with distinct hashes were a denial-of-seat case in two reviews; naming
identity by `(transfer, holder)` removes the case rather than ordering it.
Limit. A thief holding the old key can still contest a rotation by
transferring to itself. The honest holder's resign blocks both moves, and
recovery or re-grant then seats a new key (ADR-2005, ADR-2009).

**ADR-2014: An emptied seat counts as met.**
Decision. The removals that empty a member seat stand in for its act.
The fan-in's authority past holds them and no act of that seat for the
round. Accepted transfers and reseats keep the seat, and the successor
acts. A contested seat is not emptied and is not met by its removals.
Evidence. Dynamic Multirole Session Types lets a participant leave only when
its local type is `end` or at `unlock` (f-session-27). Otherwise a counting
participant waits for ever. A removal in CBCL cannot wait: a revoke answers
a stolen key (FM-4). Counted fan-in is the one R5 construct that waits on
several seats at once. A single citation of a vacant singleton waits
too, and stays a limit (Open).
Rejected. *Leave only at a safe point*: a thief holds the key, and no
protocol state is safe. *Obligations pass to the delegator*: the parent
then speaks for the child, the ambient authority FM-2 removes. *Only
resign and revoke of the warrant itself*: a revoked parent empties every share
under it by cascade, the commonest removal path. *Require the removal to
hold the anchor*: a removal concurrent with the opener then sticks the
round again.
Consequence. A collector that omits a seat's act and cites its removal
is within ADR-2011's honest-sender limit. The act stays in the log, and a
later fan-in that holds it and still omits it from its references is
`Violation`. A contested seat stays a member, so a stolen key cannot
empty a round by double transfer. The deadlock-freedom test TEST-2054 rests
on this rule.

**ADR-2015: Liveness is claimed against delivery fairness; deadlock-freedom
is tested, liveness is not proved.**
Decision. NFR-2003 names one fairness assumption and two liveness claims.
The core suite tests deadlock-freedom over finite fair schedules
(TEST-2054). Liveness over infinite traces is Open.
Evidence. The mechanised MPST result separates safety, deadlock-freedom and
liveness, defines liveness only under a fairness assumption, and needs
balanced global types (f-session-23, f-session-24). It covers environments
associated by subtyping, which is how proxies and narrowed seats relate
to the projection (f-session-25). The liveness proof is about 14K lines of
Rocq for a synchronous, static system (f-session-26). On finite typing
contexts the same properties are decidable by model checking (f-wiki-03),
which is the cheaper route for v1's finite protocols. DMst, which adds
participants by protocol call, defines liveness as no stuck participant and
notes that only receives get stuck (f-session-31).
Rejected. *No liveness statement*: SPEC-014 REQ-619 names a vacant role as
liveness and bounds nothing. *Mechanised liveness now*: out of proportion
while the Rust core has no executable warrant state.
Consequence. Balancedness guards a process that blocks on a receive; no
CBCL endpoint does, so a v1 protocol needs no such check. It returns as an
installation check if a future grammar adds blocking receives or recursion
(Open). REQ-2048 is the subtyping condition, stated per grant.

**ADR-2016: A seat is the chair; a warrant is the paper.**
Decision. *Seat* names the binding of a role that keeps its identity while
holders change. *Warrant* names one key's signed authority to send some
acts in a seat. *Proxy* names a warrant that acts in its delegator's seat.
The wire tokens follow: `:warrant` on acts and meta acts, `:replaces` on a
reseat, and mode `proxy`. No semantics changed with the words.
Evidence. Versions 0.1.0 to 0.6.0 said *position* for the binding and
*seat* for the authority, and called *seat* a coined term. The Orientation's
own metaphor put persistence on the chair and change on the slip. Everyday
English does the same: a seat on a board is taken over, and its holder
changes.
The old words inverted the metaphor, so every reader outside the spec had to
unlearn them. A warrant is a signed paper that names its holder, is issued
and withdrawn, and can be narrowed. Its nearest art is the SPKI
authorisation certificate (f-certs-01, f-certs-08). *Facet* is E-language
and Goblins jargon (f-ocap-16) and reads as "aspect" elsewhere. *Proxy* is
the plain word for one who acts for another.
Rejected. *Keep the coined usage*: it taxes every reader for no gain. *Rename
in product copy only*: reviewers and implementers read the spec, and two
vocabularies for one object double the glossary.
Consequence. The rename is total: this spec, the concept pages,
`LeanCbcl/Seats.lean` identifiers and the Rust surface (CON-2002, CON-2003).
`reseat` keeps its name and now reads literally. Client copy maps plain
requests to meta acts as the Orientation's table shows.

## Contracts

### CON-2000: Role policy grammar

Input: the SExpr AST of the dialect, after the existing reader and R1–R3.
This extends [[SPEC-014-role-layer-endpoint-projection#CON-600]]. A SPEC-014
`role-decl` remains valid and means a policy-free role.

```
roles-clause  := "(" ":roles" "(" role-decl+ ")" ")"
role-decl     := symbol                              ; singleton, policy-free (SPEC-014)
               | "(" "*" symbol policy* ")"          ; indexed (SPEC-014 when no policy)
               | "(" symbol policy+ ")"              ; singleton with policy
policy        := ":delegate" "(" mode+ ")"
               | ":appoint" "(" symbol+ ")"          ; indexed roles this role appoints into
               | ":recover-by" symbol                ; role whose root occupants reseat this one
mode          := "share" | "transfer" | "redelegate"
               | "(" "proxy" symbol+ ")"             ; acts a proxy of this role can carry
```

LL(1): after `(`, the token `*` selects an indexed declaration and any other
symbol selects a singleton with policy. Each policy keyword appears at most
once per declaration.
Pre-conditions: dialect SExpr fully recognised; R1–R3 passed.
Post-conditions: `Vec<RoleDecl>` with `RolePolicy` per role, or a violation,
with no partial result.
Error model: see [[SPEC-020-capability-seats#CON-2003]]. Fail closed, with
no repair of malformed input.
Implements: [[SPEC-020-capability-seats#REQ-2000]] through
[[SPEC-020-capability-seats#REQ-2005]], [[SPEC-020-capability-seats#REQ-2038]],
[[SPEC-020-capability-seats#REQ-2043]].
Verified by: [[SPEC-020-capability-seats#TEST-2000]] through
[[SPEC-020-capability-seats#TEST-2005]], [[SPEC-020-capability-seats#TEST-2038]],
[[SPEC-020-capability-seats#TEST-2045]] (fuzz).

### CON-2001: Cast extension and meta-act grammar

```
with-roles    := "(" "with-roles" "(" binding+ ")"
                     [":dialect" hash] [":fixed" "(" symbol+ ")"]
                     signed-form ")"

meta-act      := grant | accept | revoke | resign | reseat
grant         := "(" "grant" recipients ":role" symbol ":to" key
                     ":mode" ("proxy" | "share" | "transfer" | "appoint")
                     [":acts" "(" symbol+ ")"] [":redelegate" bool]
                     ":warrant" designation thread-attrs ")"
accept        := "(" "accept" recipients ":grant" hash thread-attrs ")"
revoke        := "(" "revoke" recipients ":grant" hash ":warrant" designation thread-attrs ")"
resign        := "(" "resign" recipients ":warrant" designation thread-attrs ")"
reseat        := "(" "reseat" recipients ":replaces" designation ":to" key
                     ":warrant" designation thread-attrs ")"
designation   := hash                                ; a grant, accept or reseat hash
               | "(" "root" symbol [key] ")"         ; a root seat; key REQUIRED when ambiguous
thread-attrs  := ":caused-by" causes [":seen" "(" hash+ ")"] ":thread" string ":sender" key
act-authority := [":warrant" designation] [":seen" "(" hash+ ")"] [":anchor" hash]   ; on a dialect act
```

Each bracketed element has one fixed place, shown above. Hash identity is
over the typed value, with these canonical rules. An omitted element is never
written, so `:redelegate #f` is written as nothing. `:acts`, `:seen` and
`:fixed` are sets and are written in bytewise ascending order. `nat` has no
leading zero. `recipients` keeps its SPEC-014 order. Two messages that differ
only in these respects are one message. A parser SHALL reject a duplicate or
misplaced authority element rather than normalise it.
`:seen` appears once per message: in `thread-attrs` on a meta act, and in
`act-authority` on a dialect act. On a dialect act the `act-authority`
elements follow `:caused-by` and precede `:thread`, before any dialect
parameter. `:anchor` appears only on a counted fan-in over a dynamic role
(REQ-2046). `recipients`, `hash`, `key`, `causes` and `string` are the
SPEC-014 and R5 productions. `:acts` omitted means the parent warrant's act set,
or all of the role's acts for `appoint`. A proxy grant never omits it
(REQ-2008). A transfer's `:to` names the one key that can accept. A
reseat's `:replaces` names the terminal warrant it replaces. A revoke's `:warrant`
names the upstream warrant its signer uses (REQ-2040).
Pre-conditions: the dialect governing the thread is installed; every meta
act is inside a `signed` wrapper (R4).
Post-conditions: a typed `MetaAct` value, or a violation.
Error model: see [[SPEC-020-capability-seats#CON-2003]]. Grammar violations
never reach semantic checks.
Implements: [[SPEC-020-capability-seats#REQ-2006]],
[[SPEC-020-capability-seats#REQ-2013]], [[SPEC-020-capability-seats#REQ-2015]],
[[SPEC-020-capability-seats#REQ-2036]].
Verified by: [[SPEC-020-capability-seats#TEST-2006]],
[[SPEC-020-capability-seats#TEST-2013]], [[SPEC-020-capability-seats#TEST-2015]],
[[SPEC-020-capability-seats#TEST-2036]], [[SPEC-020-capability-seats#TEST-2045]]
(fuzz, round-trip and canonical-equivalence oracles).

### CON-2002: Rust API surface

```rust
// role.rs (extended)
pub enum Mode { Proxy, Share, Transfer, Appoint }        // grant modes
pub enum WarrantMode { Proxy, Share, Principal }            // delegation rights: Proxy < Share < Principal
pub struct RolePolicy {
    pub modes: BTreeSet<Mode>,
    pub redelegate: bool,
    pub proxy_acts: BTreeSet<String>,
    pub appoint: BTreeSet<String>,
    pub recover_by: Option<String>,
}
impl RolePolicy { pub fn fixed() -> Self; }
pub struct RoleDecl { pub name: String, pub cardinality: RoleCardinality, pub policy: RolePolicy }
pub struct Cast {                                       // SPEC-014 fields kept
    pub singleton: BTreeMap<String, AgentKey>,
    pub indexed: BTreeMap<String, BTreeSet<AgentKey>>,
    pub dialect_pin: Option<String>,
    pub fixed: BTreeSet<String>,
}

// capability.rs (new)
pub enum Seat { Root { role: String, root_key: AgentKey }, Granted(ContentHash) }
pub enum WarrantId { Root(Seat), Grant(ContentHash), Moved(ContentHash), Reseated(ContentHash) }
pub enum ActSet { All, Only(BTreeSet<String>) }
pub struct Warrant {
    pub id: WarrantId, pub seat: Seat, pub holder: AgentKey, pub mode: WarrantMode,
    pub acts: ActSet, pub redelegate: bool,
    pub chain: Vec<WarrantId>,                              // principal warrant first, this warrant last
}
pub enum SeatStatus { Live, Contested, Emptied }
pub struct WarrantState { /* issued, removed, successors, live, terminal warrants — BTreeMap-backed */ }
pub enum CapabilityPolicy { Reject, Observe, Accept }   // installer option, default Reject
pub struct CapVerdict {
    pub admission: VerificationResult,                   // the verdict (SPEC-014's under Observe)
    pub reason: Option<CapViolation>,                    // first failing check, if any
    pub observed: Option<(VerificationResult, Option<CapViolation>)>, // SPEC-020's, under Observe
}

pub fn authority_past<S: MessageStore>(msg: &Message, thread: &ThreadId, store: &S)
    -> Result<AuthorityPast, Unresolved>;
pub fn warrant_state(d: &Dialect, root: &Cast, meta_acts: &BTreeSet<ContentHash>, store: &impl MessageStore)
    -> WarrantState;                                        // mirrors LeanCbcl/Seats.lean
pub fn seat_status(state: &WarrantState, seat: &Seat) -> SeatStatus;
pub fn anchor_walk<S: MessageStore>(act: &Message, d: &Dialect, root: &ContentHash, thread: &ThreadId, store: &S)
    -> Result<ContentHash, Unresolved>;                   // ends at the root hash or another seat's message
pub fn round_membership(d: &Dialect, root: &Cast, anchor_past: &AuthorityPast, role: &str, store: &impl MessageStore)
    -> BTreeSet<Seat>;                                // present minus emptied
pub fn choice_groups(d: &Dialect, role: &str) -> Vec<BTreeSet<String>>;   // REQ-2048
pub fn seat_cast(d: &Dialect, root: &Cast, state: &WarrantState) -> Cast; // REQ-2048, seats as entries
pub fn verify_with_capabilities<S: MessageStore>(
    msg: &Message, d: &Dialect, root_cast: &Cast, store: &S,
    thread: &ThreadId, root: &ContentHash, policy: CapabilityPolicy,
) -> CapVerdict;
```

`verify_with_capabilities` returns the admission verdict of REQ-2022. All
functions are pure given their arguments; store access is read-only through
the existing `MessageStore` trait.
Implements: [[SPEC-020-capability-seats#REQ-2007]] through
[[SPEC-020-capability-seats#REQ-2049]] except the grammar and consumer REQs.
Verified by: [[SPEC-020-capability-seats#TEST-2007]] through
[[SPEC-020-capability-seats#TEST-2058]].

### CON-2003: Capability error model

`CapViolation` SHALL be an enum with one variant per rejecting condition.
Grammar and cast errors reuse the SPEC-014 `R6Violation` variants
`MalformedCast` and `UnknownRole`
([[SPEC-014-role-layer-endpoint-projection#CON-603]]). Checks run in table
order; the first failure is the reason (OBS-2000).

| Variant | Rejecting condition |
|---|---|
| `MalformedPolicy` | CON-2000 grammar |
| `PolicyNamesUnknownRole` | REQ-2003, undeclared role |
| `ProxyActNotInRole` | REQ-2003, act of another role |
| `ProxyOverChoice` | REQ-2003, singleton choice act |
| `ShareOnSingleton` | REQ-2004 |
| `DynamicRoleInFanIn` | REQ-2005, walk meets a stop |
| `MixedRoleFanIn` | REQ-2005, two roles counted |
| `RecoveryRoleInvalid` | REQ-2038 |
| `ReservedName` | REQ-2043 |
| `MalformedMetaAct` | CON-2001 grammar, duplicate or misplaced element |
| `CapabilitiesDisabled` | REQ-2035 |
| `Inherited(R6Violation)` | SPEC-014 role, cast or R5 failure (REQ-2022) |
| `CrossThreadLink` | REQ-2044 |
| `NotAWarrant` | REQ-2014 |
| `AmbiguousRoot` | REQ-2015 |
| `HolderMismatch` | REQ-2016 |
| `WarrantRoleMismatch` | REQ-2013, role differs |
| `WarrantNotLive` | REQ-2017, REQ-2023 |
| `ActNotCovered` | REQ-2013, act outside the warrant |
| `RecipientMismatch` | REQ-2021 |
| `IssuerLacksWarrant` | REQ-2007 |
| `ModeNotPermitted` | REQ-2001, REQ-2006, REQ-2008, REQ-2039: mode, role or rights |
| `ProxyActNotPermitted` | REQ-2008, act outside the proxy list |
| `WideningGrant` | REQ-2009 |
| `RedelegateNotPermitted` | REQ-2010 |
| `ChainTooLong` | REQ-2011 |
| `UnliveGrant` | REQ-2048, choice group lost |
| `NotCausallyLocal` | REQ-2048, carries the `R6Violation` |
| `MetaActRecipientMismatch` | REQ-2032 |
| `TransferNotAccepted` | REQ-2020 |
| `AcceptNotPermitted` | REQ-2045 |
| `LacksAuthorityToRemove` | REQ-2040 |
| `ReseatNotPermitted` | REQ-2031 |
| `AnchorMissing` | REQ-2046, no `:anchor` on a dynamic fan-in |
| `AnchorInvalid` | REQ-2046, wrong performative or outside the past |
| `MixedRounds` | REQ-2046, a walk ends elsewhere |
| `SeatOutsideRound` | REQ-2041 |
| `MissingMember` | REQ-2041, REQ-2047: a member neither acted nor emptied |

Each variant carries the names needed to locate the defect.

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `role.rs`: policy parsing, cast extension parsing
- `capability.rs`: meta-act parsing, authority past, `warrant_state`,
  `seat_status`, `anchor_walk`, `round_membership`, `choice_groups`,
  `seat_cast`, designation
- `projection.rs`: `project` unchanged; `verify_with_capabilities` composes it

### Effectful Shell (orchestrates I/O, calls pure core)
- Consumers (cbcl-bus, hark): store the log, deliver to recipients, proxy
  holders and new warrant holders (REQ-2042), count rejections, notify holders
  before refusing them.

### Boundary Contracts
`Message`, `ContentHash`, `MessageStore` (read-only), `CapVerdict`,
`CapabilityPolicy`.

### Dependency Rule
The pure core reads nothing but its arguments and the store. No participant
other than the signers of the messages in `A(m)` influences a verdict.

### Enforcement
`capability.rs` imports nothing outside `cbcl-core`; review checks this.

## Test Specifications

Each example-based test below pairs with the REQ of the same number. A `b`
suffix, or a number from 2046, marks a test for a REQ numbered in the 2040s.
Each covers the positive case, the negative-input case and, where the REQ
prohibits an action, the prohibited case. Fixtures extend the SPEC-014
`checklist` and auction corpora with an incident dialect. Its roles are:
- `commander`, singleton: `:delegate (transfer (proxy assign))
  :recover-by observer :appoint (responder)`;
- `responder`, indexed: `:delegate (share redelegate (proxy finding))`;
- `observer`, indexed, policy-free, with a Send performative `note`.
Its protocol has three steps. `request :from commander :to (responder
observer)`. `report :from responder :to (commander observer)` with
predecessor `request`. `close :from commander :to (responder observer)`
over `(all report)`. `finding` and
`propose-fix` are responder sends with predecessor `request`, declared as
one choice ([[SPEC-014-role-layer-endpoint-projection#REQ-603]]) and
addressed to commander and observer. `assign` is a commander send with
predecessor `report`, addressed to responder. `resolve` and `dismiss` are a
commander choice with predecessor `close`. Responder's choice groups are
therefore `{report}` and `{finding, propose-fix}`. Every fixture cast lists
three root responders, @eli, @fay and @gus, unless a test says otherwise.
The dialect installs under SPEC-014 locality before any grant.

**Core** (writable in one sitting with the existing test harness): every
example test below.
**Depth** (needs proptest generators, fuzz targets or Lean work; owner HOC):
TEST-2040, TEST-2041, TEST-2043 through TEST-2045, the property half of
TEST-2054, and the Lean obligations in Open.

**TEST-2000: Policy parses.** Positive: the incident dialect yields the
stated `RolePolicy` per role. Negative: a duplicate `:delegate` clause
yields `MalformedPolicy`.

**TEST-2001: Policy-free default.** Every SPEC-014 fixture dialect yields
`RolePolicy::fixed()` for every role. A `resign` of an observer root warrant
yields `ModeNotPermitted`.

**TEST-2002: Policy is signed.** Stripping `:delegate` from a signed dialect
fails R4 verification.

**TEST-2003: Policy names declared things.** `:appoint (ghost)` yields
`PolicyNamesUnknownRole`. `(proxy finding)` on `commander` yields
`ProxyActNotInRole`. `(proxy resolve)` on `commander` yields
`ProxyOverChoice`.

**TEST-2004: Indexed targets only.** `commander :delegate (share)` yields
`ShareOnSingleton`. `:appoint (commander)` yields `ShareOnSingleton`.

**TEST-2005: Anchored rounds only.** The auction dialect with
`(* bidder :delegate (share))`, whose counted `reveal` follows one act,
installs, and its static walk ends at `open`. Each of these variants yields
`DynamicRoleInFanIn`. The counted performative follows an `(all …)` step.
It follows a two-alternative predecessor list. It follows a performative of
another indexed role. An `(all report note)` that counts responder and
observer together yields `MixedRoleFanIn`. With
`(* bidder :delegate (transfer))`, the original installs.

**TEST-2006: Cast extension.** A root with `:fixed (responder)` parses. Then
a share grant in `responder` is rejected with `ModeNotPermitted`, and so is
a reseat of a `:fixed` commander. `:fixed (ghost)` yields `MalformedCast`.

**TEST-2007: Issuer holds the warrant.** Positive: root responder @eli grants a
share to @diag. Negative: @cy, holding no responder warrant, grants and gets
`IssuerLacksWarrant`.

**TEST-2008: Mode and acts permitted.** A `transfer` grant in `responder`
yields `ModeNotPermitted`. A `share` issued under a proxy warrant yields
`ModeNotPermitted`. A commander proxy grant without `:acts` yields
`MalformedMetaAct`. One with `:acts (resolve)` yields `ProxyActNotPermitted`.

**TEST-2009: Never widen.** A proxy `(finding)` parent with a child granting
`(finding propose-fix)` yields `WideningGrant`. A child with
`:redelegate #t` under a parent with `#f` yields `RedelegateNotPermitted`
(REQ-2010 runs first) and, with the parent flag forced on for the fixture,
`WideningGrant`.

**TEST-2010: Redelegate bit.** A child of a grant issued with
`:redelegate #f` yields `RedelegateNotPermitted`.

**TEST-2011: Chain bound.** A chain of 8 grants resolves. A chain of 9
yields `ChainTooLong`.

**TEST-2013: Designation and confused deputy.** @diag holds proxy G1
`(finding)` from @eli and share G2 from @cy. An act `propose-fix :warrant G1`
is a `Violation` with `ActNotCovered`, even though G2 covers it. The same
act under G2 is `Valid`. A `resolve` act `:warrant G2` yields
`WarrantRoleMismatch`.

**TEST-2014: Designation resolves.** An act naming a dialect act yields
`NotAWarrant`.

**TEST-2015: Root designation.** For @dana, holding one commander seat,
`:warrant (root commander)`, `:warrant (root commander @dana)` and an omitted
`:warrant` give equal verdicts. A key holding two responder seats that
omits `:warrant` yields `AmbiguousRoot`.

**TEST-2016: Holder ratified by signature.** An act signed by @x with
`:sender @diag` under @diag's grant yields `HolderMismatch`.

**TEST-2017: Warrant state is order-independent.** Every permutation of a set
with three grants, one accept and one revoke yields equal warrant states. After
an accepted transfer, the `Moved` warrant is live and not removed by its own
accept. The Rust `warrant_state` agrees with `LeanCbcl/Seats.lean` on a table
of twelve hand-built sets covering each rule of REQ-2017 and REQ-2037.

**TEST-2018: Projection unchanged.** `project` output for every role equals
the SPEC-014 output. A proxy `(finding)` holder's Send set is `{finding}`.

**TEST-2019: Root seat holders.** A `revoke` whose `:grant` names the
root wrapper hash yields `NotAWarrant`. After @dana's accepted transfer to
@fay, an act by @fay under the `Moved` warrant is `Valid`. An act by @dana
under `(root commander)` whose past holds the accept yields `WarrantNotLive`.

**TEST-2020: Transfer on accept.** @dana offers commander to @fay with
`:acts (assign resolve dismiss) :redelegate #f`. Before the accept: @dana
`resolve` is `Valid` and @fay `resolve` under the transfer grant yields
`TransferNotAccepted`. After the accept, the reverse holds. @fay's `request`
under the `Moved` warrant yields `ActNotCovered`, and @fay's proxy grant
yields `RedelegateNotPermitted`. A proxy @dana issued before the transfer is
removed; a proxy @dana issues after it yields `IssuerLacksWarrant`.

**TEST-2021: Recipients and delivery.** After a share to @diag, a
responder-addressed act that omits @diag yields `RecipientMismatch`. After
a proxy to @tidy, the delivery set of a commander-addressed act includes
@tidy and its recipient set does not. With the commander seat contested,
a commander-addressed act needs no commander recipient.

**TEST-2022: Admission verdict composes.** A role-conformant act under a
live warrant is `Valid`. The same act with a protocol-order error is
`Violation` with `Inherited(InvalidPredecessor)`. An act that fails both the
protocol order and warrant liveness carries the inherited reason, which comes
first in the table.

**TEST-2023: Removal in authority past.** After R1 revokes G1, an act under
G1 with R1 in `:seen` yields `WarrantNotLive`. So is an act under G2 whose chain
contains G1. An act under G1 without R1 in its authority past is `Valid`.

**TEST-2024: Admission monotone.** Adding unrelated messages to the store
never changes a `Valid` admission verdict.

**TEST-2031: Reseat.** Observer @oli reseats the commander seat of @dana
to @dana2 with `:replaces (root commander @dana)`. Three things hold for a
message whose authority past holds the reseat. Acts by @dana under the root
warrant are `WarrantNotLive`. A proxy issued under @dana's warrant is removed. An act
by @dana2 under the `Reseated` warrant is `Valid`. An act by @dana whose past
lacks the reseat stays `Valid`. A reseat by a non-observer, of a `:fixed`
role, or naming a warrant that is not the seat's terminal warrant, yields
`ReseatNotPermitted`. After @dana's accepted transfer to @fay, a reseat
naming the `Moved` warrant is admitted and one naming the root warrant is
`ReseatNotPermitted`. A reseat of a contested commander seat puts
@dana2 in it alone.

**TEST-2032: Meta acts reach everyone affected.** A grant whose recipients
omit a root occupant or the grantee yields `MetaActRecipientMismatch`. A
revoke whose recipients omit the revoked holder yields the same, and so does
a reseat that omits its `:to` key.

**TEST-2033: Revocation follows the chain.** @eli revokes G3, issued by
@diag under G1, which @eli issued. Admitted. @cy revokes G1 and gets
`LacksAuthorityToRemove`. Revoking G1 removes G3. @dana revokes her own
transfer offer T before @fay accepts: the accept yields `AcceptNotPermitted`.
When the accept is concurrent with the revoke, the accept stands and the
warrant moves.

**TEST-2034: Conservative extension.** For every non-meta message without
`:warrant`, `:seen` or `:anchor` in the SPEC-014 fixture corpus, the admission
verdict equals `verify_causal_for_role`.

**TEST-2035: Opt-in installation.** With the default `Reject`, the incident
dialect fails installation with `CapabilitiesDisabled`. With `Accept`, it
installs. A policy-free dialect installs under both.

**TEST-2036: Authority links outside R5.** A protocol-valid `finding` with
`:warrant G1 :seen (R0)` has the same R5 verdict as without those links. The
same act citing G1 in `:caused-by` is the R5 `InvalidPredecessor`.

**TEST-2037: Dominance among terminations.** @dana's two transfers to @fay
and @gus are both accepted. A message whose authority past holds both
accepts finds the commander seat contested: acts under either `Moved`
warrant yield `WarrantNotLive`. @dana's resign concurrent with @fay's accept
empties the seat, and @fay's act under the `Moved` warrant is
`WarrantNotLive`. Observer @oli's reseat concurrent with both accepts seats its
`:to` key, and acts under it are `Valid`. Two concurrent reseats by @oli
and @ora contest the seat. @fay's two accepts of one transfer, with
different `:seen` lists, are one termination. Acts under the `Moved`
warrant named by the lower hash are `Valid` in a past holding both.

**TEST-2038: Recovery role.** `commander :recover-by observer` with
`observer :recover-by commander` yields `RecoveryRoleInvalid`. A role
recovering itself, and a receive-only recovery role, yield the same.

**TEST-2039: Appointment.** @dana appoints @new to responder with
`:mode appoint`: admitted, and @new can send `finding`. Revoking that
appointment removes @new. The same grant under an observer warrant yields
`ModeNotPermitted`. @new, appointed with `:redelegate #t`, shares its
seat to @new2: admitted. With responder's policy reduced to
`(redelegate (proxy finding))`, the same share yields `ModeNotPermitted`.

**TEST-2042b: Authority past delivery.** A consumer harness seats @new by
appointment. @new's verifier, given only what the harness delivered, admits
@new's first act rather than returning `Unknown`.

**TEST-2043b: Reserved names.** A dialect declaring a performative `grant`
yields `ReservedName`. So does one declaring a parameter `anchor` on any
performative.

**TEST-2044b: Thread scope.** An act whose `:seen` names a revoke of another
thread yields `CrossThreadLink`. An act whose `:seen` target is absent is
`Unknown`.

**TEST-2048: Accept admission.** @x, holding no warrant, issues a transfer of
the commander warrant to @x2, which @x2 accepts. The transfer yields
`IssuerLacksWarrant` and the accept `AcceptNotPermitted`; commander stays with
@dana. An accept signed by a key other than the grant's `:to` yields
`AcceptNotPermitted`. An accept of a valid transfer whose parent warrant is
removed in the accept's past yields `AcceptNotPermitted`. An accept whose
past holds a revoke of the transfer yields `AcceptNotPermitted`. A valid
accept is admitted and the `Moved` warrant is live.

**TEST-2049: Two-hop contest.** Concurrent accepts move commander to @fay and
@hal. @fay moves on to @fay2 and @hal to @hal2. A message whose authority
past holds all four finds the root warrant contested, neither `Moved` warrant
issued, and neither second-hop warrant issued. The warrant state lists exactly
the root warrant as issued for the seat.

**TEST-2050: Share chain.** @dana appoints @new to responder; @new shares to
@new2. Revoking @new's appointment removes @new2's warrant by cascade, and
@new2's seat is emptied, not contested. Reseating the commander seat
removes both. A share's issuer's upstream can revoke the share.

**TEST-2046: Resign requires the warrant.** @cy resigns @eli's warrant and gets
`LacksAuthorityToRemove`. @eli, after an accepted transfer of its warrant to
@fay, resigns with the accept in its past and gets
`LacksAuthorityToRemove`. @diag, holding share G2, resigns G2: admitted.

**TEST-2047: Fan-in counts seats.** In the auction with
`(* bidder :delegate (share transfer))` counted by `(all reveal)`, a proxy
act satisfies its delegator's seat. A transferred warrant's act satisfies
the original seat. Two reveals from one seat count once. A
`declare-winner` that references a reveal from a seat shared in after
the anchor is `SeatOutsideRound`. One that references no reveal from a
live member, and holds no discharge of it, is `MissingMember`. The result
carries the full fan-in verdict, not only a count.

**TEST-2051: Round anchor.** @eli shares responder to @diag before @dana's
`request`, and the share is in `A(request)`. A `close :anchor request`
without @diag's `report` is `MissingMember`; with it, `Valid`. In a second
thread the share follows the request: `close` is `Valid` without @diag, and
a `close` that references @diag's `report` is `SeatOutsideRound`. A
`close` whose referenced reports walk to two different requests yields
`MixedRounds`. A `close` with no `:anchor` over a dynamic role yields
`AnchorMissing`; one over the policy-free observer omits it and counts the
root seats. A `close` that references no report, cites @eli's and
@fay's resigns, and names the root as anchor, yields `AnchorInvalid`. The
static walk ends at `request`, not the root. In the auction, each `reveal`
walks through its own `commit` to `open`, and `declare-winner :anchor open`
is `Valid`. A contested responder seat in `A(request)` is a member, and
a `close` that lacks its report is `MissingMember`.

**TEST-2052: Discharge.** Root responder @eli resigns after the request. A
`close` referencing the other reports, with the resign in its authority
past, is `Valid`. Without the resign it is `MissingMember`. When @eli's
`report` is also in the close's authority past and the close omits it, the
close is `MissingMember`. @cy's revoke of a shared warrant yields
`LacksAuthorityToRemove` and discharges nothing. Revoking the share's parent
discharges the share. After an accepted transfer of @eli's warrant to @fay2,
@fay2's `report` satisfies the seat. An @eli act whose authority
past holds the accept is `Violation`. After that transfer, @fay2's resign
of the `Moved` warrant discharges the seat. A seat contested by two
accepts and then emptied by a cascade from its parent is discharged. Three
resigns and a `close` that references no report, with all three in its
past, is `Valid` (TEST-2056).

**TEST-2053: Unlive grant.** Responder's choice groups are `{report}` and
`{finding, propose-fix}`. A `share` with `:acts (finding)` yields
`UnliveGrant`; with `:acts (finding report)` it is admitted. A `transfer` of
commander with `:acts (assign)` yields `UnliveGrant`. A `proxy` with
`:acts (finding)` is admitted. A share whose new seat fails
[[SPEC-014-role-layer-endpoint-projection#REQ-608]] on the
[[SPEC-014-role-layer-endpoint-projection#TEST-641]] shape yields
`NotCausallyLocal`. With @eli holding two responder seats, the seat
cast passed to REQ-608 has two responder entries. A third share by @eli
is checked against both.

**TEST-2054: Deadlock-freedom.** Core, scripted: @dana's `request` is the
anchor; then @eli shares to @diag, @fay resigns, and @eli's share is
revoked, delivered in every order. A `close :anchor request` is `Valid`
exactly when its authority past holds @fay's resign and the reports of @eli
and @gus; @diag's seat is outside the round. A second script revokes
@gus's seat through a cascade from an appointer and asserts the same
shape. Depth, property: random grants, removals and acts under a scheduler
that delivers every message. No thread ends with an `Unknown` whose
authority past and anchor past are present. Every generated round with
no contested member admits some `Valid` close.

**TEST-2055: Liveness claims.** A `finding :warrant G1` with G1 arriving
last is `Unknown` until then and `Valid` after. A `close` whose anchor's
authority past is incomplete is `Unknown` until it completes, and then
`Valid` or `Violation` with the reason the fixture expects. A round with a
contested member admits no `Valid` close until a reseat lands, and then
does.

**TEST-2056: Anchored fan-in and R5.** In a three-responder cast, all three
resign without reporting. A `close :anchor request` with an empty
`:caused-by` and the three resigns in its past is `Valid`. The same close
with a `request` in `:caused-by` is `Inherited(InvalidPredecessor)`. A
`close` over the policy-free observer with an empty `:caused-by` is the
unchanged R5 `Violation`.

**TEST-2057: Seat cast.** With @eli holding root seat P1 and shared
seat P2, `seat_cast` yields two responder entries. After P1 moves
to @fay, the cast still yields two entries and neither is keyed by @eli.

**TEST-2058: Observe mode.** Under `Observe`, an act under a revoked warrant
returns admission `Valid` (SPEC-014's verdict) and `observed` carrying
`Violation` with `WarrantNotLive`. Under `Accept`, the same act returns
`Violation`. Under `Reject`, the dialect does not install.

**TEST-2040: Narrowing property (depth).** Take random chains within one
role. The reduced warrant's act set is the intersection of every link. Its
delegation rights are the minimum over the chain.

**TEST-2041: Determinism and order-independence property (depth).** Take
random logs that include concurrent accept/accept, accept/reseat,
resign/accept and revoke/accept pairs. Every admission verdict is equal
across delivery permutations. `warrant_state` is equal across
permutations of each authority past.

**TEST-2043: Designation cost guard (depth).** Operation counts for chain
lengths 1 through 8 stay within the NFR-2000 bound.

**TEST-2044: Typed reasons (depth).** Each rejecting fixture yields exactly
one `CapViolation` variant, matching the table in CON-2003. A fixture that
fails two rows yields the earlier row's variant.

**TEST-2045: Grammar fuzz (depth).** A fuzz target over CON-2000 and
CON-2001 with three oracles. `parse(serialise(x)) == x`. A message with a
duplicate or misplaced authority element is rejected. Two serialisations
that differ only in set order, numeral form or an omitted default hash
equal.

## Traceability

| REQ | CON | TEST | Failure mode | Evidence |
|-----|-----|------|--------------|----------|
| REQ-2000–2003, 2043 | CON-2000, CON-2003 | TEST-2000–2003, 2043b, 2045 | FM-1 | ADR-2000, ADR-2007 |
| REQ-2004, 2039 | CON-2000, CON-2002 | TEST-2004, 2039 | FM-1 | ADR-2002, ADR-2007 |
| REQ-2005, 2041, 2046, 2049 | CON-2000, CON-2001, CON-2002, CON-2003 | TEST-2005, 2047, 2051, 2056 | FM-1, FM-6 | ADR-2006 |
| REQ-2047 | CON-2002 | TEST-2052, 2054 | FM-6 | ADR-2014 |
| REQ-2048 | CON-2002, CON-2003 | TEST-2053, 2057 | FM-6 | ADR-2015 |
| NFR-2003 | CON-2002 | TEST-2054, 2055 | FM-6 | ADR-2015 |
| REQ-2038, 2031 | CON-2000, CON-2002 | TEST-2038, 2031 | FM-4 | ADR-2009 |
| REQ-2006 | CON-2001 | TEST-2006 | FM-1 | ADR-2011 |
| REQ-2036, 2044, 2042 | CON-2001, CON-2002 | TEST-2036, 2044b, 2042b | FM-1, FM-2, FM-3 | ADR-2012 |
| REQ-2007–2011 | CON-2002 | TEST-2007–2011, 2040 | FM-2 | ADR-2001, ADR-2002 |
| REQ-2013–2016 | CON-2001, CON-2002 | TEST-2013–2016 | FM-2 | ADR-2003 |
| REQ-2017–2021, 2032, 2040 | CON-2002 | TEST-2017–2021, 2032, 2033, 2046, 2041 | FM-1, FM-4 | ADR-2000, ADR-2007, ADR-2008, Seats.lean |
| REQ-2037, 2045 | CON-2002 | TEST-2037, 2048, 2049, 2050 | FM-4, FM-5 | ADR-2005, ADR-2013, Seats.lean |
| REQ-2022–2024 | CON-2002, CON-2003 | TEST-2022–2024, 2041, 2044 | FM-3 | ADR-2004, ADR-2011 |
| REQ-2034 | CON-2002 | TEST-2034 | — | SPEC-014 Lean correspondence |
| REQ-2035 | CON-2002 | TEST-2035, 2058 | — | enable path |

Withdrawn in 0.6.0, never reused: REQ-2012, REQ-2025 through REQ-2030,
OBS-2001, TEST-2012, TEST-2025 through TEST-2030, TEST-2042.

Reading paths. Reviewer: the ADRs, then Open, then REQ-2017, REQ-2037 and
REQ-2046. Implementer: CON-2000 → CON-2001 → CON-2002 → REQ-2017 →
`LeanCbcl/Seats.lean` → the core tests in number order. Stakeholder: the
failure modes in Context, then the Traceability table's failure-mode column.

## Appendix A: Literature evidence

The elephant theory `cap-epp-lit` holds every source and finding as signed
facts (`source-doc/2`, `says/3`, `supports/2`, `opposes/2`, `violates/2`). It
also holds the questions, options and the thirteen `chosen/2` decisions; the
rule `r-adopted` derives `adopted` for each. Regenerate this appendix with
`elephant -t cap-epp-lit --json log`.

| Question | Adopted option | Key findings |
|----------|----------------|--------------|
| Authority primitive | role as named capability (ADR-2000) | f-session-01, 10, 14, 16, 22; f-ocap-05, 09 |
| Delegation | grants in the signed log (ADR-2001) | f-conv-02, 24; f-certs-15, 28; f-session-18, 21 |
| Attenuation | act subset by intersection (ADR-2002) | f-certs-01–04, 10, 22; f-ocap-16; f-conv-32 |
| Revocation | remove-wins in the authority past, no orderer (ADR-2004, ADR-2011) | f-conv-11, 26, 27; f-ocap-18, 19; f-wiki-05 |
| Concurrency | ancestor dominance: reseat wins, kills block, equals contest (ADR-2005) | f-wiki-01, 02; f-conv-07, 12, 14, 17, 18 |
| Projection with change | membership from the authority past (REQ-2017) | f-session-02, 05, 07, 18–21 |
| Designation | explicit `:warrant` (ADR-2003) | f-ocap-01–06; f-certs-08, 14, 21, 23; f-conv-24 |
| Recovery | declared higher role (ADR-2009) | f-certs-30, 32, 33 |
| Read vs send | separate (ADR-2010) | f-conv-03, 04, 05, 29 |
| Round membership | seats present at the round anchor (ADR-2006) | f-session-02, 28, 29 |
| Removal mid-round | the removal discharges (ADR-2014) | f-session-27 |
| Liveness | claims under named fairness (ADR-2015) | f-session-23, 24, 26; f-wiki-03, 04 |
| Seat liveness | subtype check at grant (REQ-2048) | f-session-25 |

Sources (52), grouped as the survey cited them:

- Certificates and tokens:
  - SPKI RFC 2693
  - UCAN core, delegation, invocation and revocation specifications
  - W3C CCG zcap
  - Biscuit
  - Macaroons (NDSS 2014)
  - Keybase downgrade leases and teams
  - KERI
- Convergent access control:
  - Keyhive notebook
  - p2panda access control
  - Matrix state resolution v2, server-server API, Project Hydra and room version 12
  - ERA (PaPoC 2026)
  - Jacob and Hartenstein (CODASPY 2025)
  - Jacob, Stuber and Hartenstein (PaPoC 2026)
  - Byzantine Eventual Consistency
  - CALM
  - DCGKA (CCS 2021)
  - RFC 9420
  - Meadowcap
- Object capabilities:
  - Miller, Robust Composition
  - Capability Myths Demolished
  - The Confused Deputy
  - Redell 1974
  - Close, ACLs don't
  - Karp et al., ZBAC
  - Horton
  - OCapN CapTP and Locators
  - Jia et al. (PLDI 2026)
- Session types and protocols:
  - Honda, Vasconcelos and Kubo 1998
  - Deniélou and Yoshida, POPL 2011
  - parameterised MPST
  - Hu and Yoshida 2017
  - Capecchi, Castellani and Dezani
  - Bocchi et al.
  - Multiparty Session Actors
  - role-parametric session types in Go
  - global types with internal delegation
  - dynamically updatable MPST
  - procedural choreographies
  - MPST with a Bang
  - Keskin, Yoshida and van Glabbeek, ITP 2026 (Rocq liveness)
  - Scalas and Yoshida, POPL 2019 (behavioural typing contexts, mpstk)
  - Bartolo Burlò, Francalanza and Scalas, ECOOP 2021 (monitorability)
  - Singh, AAMAS 2012 (information-based protocol semantics)
  - Singh, Christie and Chopra 2026 (Langshaw: sayso and conflict)

Full citations with URLs are in the theory's `source-doc` facts.

## Changelog

<details>
<summary>Revision history — 0.1.0 → 0.7.0</summary>

- 0.7.0 (2026-10-18) — normative. Vocabulary only; no semantics changed
  (ADR-2016, new). *Position* is now *seat*; *seat* is now *warrant*;
  *facet* is now *proxy*. Wire tokens: `:under` is `:warrant` on acts, grants,
  revokes and reseats. `:seat` is `:warrant` on a resign and `:replaces` on a
  reseat. Mode `facet` is `proxy`. The reserved parameters are `warrant`,
  `seen`, `anchor` and `replaces`. Rust names follow (`Seat`, `Warrant`,
  `WarrantId`, `WarrantState`, `SeatStatus`, `warrant_state`, `seat_status`,
  `seat_cast`, `WarrantNotLive`, `NotAWarrant`, `WarrantRoleMismatch`,
  `IssuerLacksWarrant`, `SeatOutsideRound`, `ProxyActNotInRole`,
  `ProxyOverChoice`, `ProxyActNotPermitted`). `Seats.lean` identifiers
  follow. The Orientation gains a table of plain requests against meta acts
  (the role reading and the capability reading of one state).
- 0.6.0 (2026-10-18) — normative. Owner decision: no orderer. Fifth
  adversarial review (Codex, 6 blockers, 14 major, 2 minor, on the whole of
  v0.5.0) applied. Changes:
  - the arbiter, epochs, the epoch fold, the finality verdict, `:until` and
    equivocation evidence withdrawn (REQ-2012, REQ-2025 through REQ-2030,
    OBS-2001); v0.5.0 holds the design for an OPTIONAL extension
  - the warrant-state function restated from `LeanCbcl/Seats.lean`: inductive
    issuance, cascade closure, a single reseat dominates, kills block
    accepts, equals contest; removal monotone (REQ-2017, REQ-2037)
  - reseat names the terminal warrant it replaces and takes effect at
    admission (REQ-2031); withdrawal of a transfer offer (REQ-2040)
  - a moved warrant carries the transfer's narrowing (REQ-2020); warrant modes and
    delegation rights replace the mode-strength axis (REQ-2008, REQ-2009,
    REQ-2039)
  - seat status (live, contested, emptied) from the terminal warrant;
    discharge restated (REQ-2047)
  - anchor performative fixed by the static walk and checked with zero
    counted acts; mixed-role conjunctions rejected; per-performative
    coverage; `MissingMember` (REQ-2005, REQ-2041, REQ-2046)
  - anchored fan-in composes with R5 (REQ-2049, new)
  - seat cast for REQ-608; choice groups named apart from SPEC-014's
    Send step (REQ-2048)
  - one accept per `(transfer, holder)` (REQ-2045, ADR-2013)
  - canonical hashing rules and reserved `anchor` and `warrant` parameters
    (CON-2001, REQ-2043); check order and inherited reasons (OBS-2000,
    CON-2003)
  - observe mode and the enable path (REQ-2035); policy-free roles admit no
    meta act (REQ-2001, REQ-2006)
  - fixtures completed (choice, endpoints, three responders); TEST-2056
    through TEST-2058 added; adequacy findings applied across the suite
  - four wiki sources added (f-wiki-01 to f-wiki-05)

- 0.5.0 (2026-10-18) — normative. Two further session-type sources read in
  full (Deniélou and Yoshida §5; Keskin, Yoshida and van Glabbeek, ITP
  2026). Changes:
  - round anchors named by `:anchor`, anchor walks and round membership
    (REQ-2046); dynamic roles feed fan-in through anchored rounds (REQ-2005,
    REQ-2041, ADR-2006 rewritten). TEST-2005's share-auction case now
    installs. REQ-2041 counts round membership instead of root seats
  - an emptied seat counts as met (REQ-2047, ADR-2014); finality
    re-checks counted acts and discharges (REQ-2025)
  - principal warrants keep one act per Send step; REQ-608 at grant (REQ-2048)
  - named fairness and liveness claims (NFR-2003, ADR-2015); FM-6
  - `warrant` recorded as a coined term; rotate mode, balancedness and Lean
    liveness added to Open
  - fourth adversarial review (2 blockers, 15 major, 10 minor) applied in
    this version; v0.4.0's round-3 fixes remained unreviewed until round 5

- 0.4.0 (2026-10-17) — normative. Third adversarial review (4 blockers, 9
  major, 9 minor) and third comprehension gate (passed). Changes:
  - accept admission (REQ-2045); inductive issuance along replacement
    chains; share chains; root designations resolved in the authority past
  - one-pass epoch fold in authority order; entries checked against their
    own admission; expiry in the fold; reseat as an admission termination
  - canonical authority-link list; warrant attributes for root, moved and
    reseated warrants; reserved `under` and `seen` parameters
  - remaining minor findings recorded in Open

- 0.3.0 (2026-10-17) — normative. Second adversarial review (16 new
  findings, 4 blockers) and second comprehension gate addressed. Changes:
  - the warrant-state function (REQ-2017) with warrant ids for moved and reseated
    warrants and order-free terminations
  - the epoch fold (REQ-2027) and a positive finality rule (REQ-2025) that
    never consults admission
  - epochs list every removal (REQ-2026)
  - in-thread authority links (REQ-2044) and authority-past delivery
    (REQ-2042)
  - appointment as its own mode (REQ-2039)
  - no proxies over singleton choices (REQ-2003)
  - sending, acyclic recovery roles (REQ-2038)
  - reserved names (REQ-2043)
  - explicit root designation when ambiguous (REQ-2015)
  - Orientation glossary and stolen-key behaviour
- 0.2.0 (2026-10-17) — normative. First adversarial review (19 findings, 5
  blockers) and the first comprehension gate addressed. Authority links,
  cascading removal, contested seats, explicit epoch order, expiry,
  proxy act lists, fan-in by seats.
- 0.1.0 (2026-10-17) — first draft, from the `cap-epp-lit` literature
  survey. Normative.
</details>
