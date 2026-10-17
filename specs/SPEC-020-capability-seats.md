---
id: SPEC-020
title: Capability Seats — Delegable Authority for Role-Based Endpoint Projection
status: draft
version: 0.5.0
date: 2026-10-18
author: Anuna Research (https://anuna.io)
depends-on:
  - SPEC-014 (role layer — R6, endpoint projection, cast binding)
  - SPEC-002 (structural contracts — causal protocols, R5 verifier)
  - SPEC-003 (verification lattice — three-valued result, monotonicity)
refines:
  - SPEC-014 REQ-608, REQ-612, REQ-614, REQ-615, REQ-618, REQ-619, and the immutable-binding clause of REQ-613
prior-art:
  - elephant theory cap-epp-lit (48 sources, 122 findings, 13 adopted options; evidence digest in Appendix A)
  - specs/SPEC-014-role-layer-endpoint-projection.md
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
replica reaches the same verdict on every message. Roles stay the unit of
[[endpoint-projection|endpoint projection]]. Authority to act in a role
becomes a [[capability-seat|seat]], a [[object-capability|capability]] that
signed meta acts issue, narrow and remove.

Metaphor: the score stays fixed, and the chairs in the orchestra change
hands. Each player shows the signed slip that seated them. A clerk stamps
the minute-book so that disputes over who left first have one answer.

Structure:

```
 dialect (installed, pinned)                 thread log (signed DAG)
┌────────────────────────────┐             ┌─────────────────────────────────┐
│ :roles + policy clauses    │             │ with-roles root cast (+arbiter) │
│ (CON-2000) install checks  │             │ grant/accept/revoke/resign/     │
│ projection per ROLE        │             │ reseat/epoch meta acts (CON-2001)│
│ (SPEC-014 project, as-is)  │             └───────────────┬─────────────────┘
└─────────────┬──────────────┘                             │ in-thread authority links
              │                                            ▼
              │                       ┌─────────────────────────────────────┐
              │                       │ seat_state over a set (REQ-2017)    │
              │                       │ epoch fold, listed order (REQ-2027) │
              │                       └───────────────┬─────────────────────┘
              ▼                                       ▼
┌──────────────────────────────────────────────────────────────────────────┐
│ verify_with_capabilities (CON-2002) → admission verdict + finality verdict│
└──────────────────────────────────────────────────────────────────────────┘
   arrows point inward → pure core; store access read-only; the arbiter is a
   thread participant, never a dependency of cbcl-core
```

Terms used below:

- **Position**: one role binding, such as "commander, as first given to
  @dana". Root positions come from the cast; `share` and `appoint` grants
  create more. A position persists; the key holding it changes.
- **Seat**: a key's authority to send some acts of one role. Each seat belongs to a position. `share` and `appoint` grants create new positions; a facet is its own seat inside its delegator's position: its acts name the facet grant with `:under` and count as the delegator's position. The word is coined here.
- **Modes of grant**: `facet` lets a key send listed acts *as* the
  delegator's seat. `share` adds a co-occupant of an indexed role. `transfer`
  hands a seat to another key once that key accepts. `appoint` adds an
  occupant to another indexed role that the dialect allows. `facet`, `share`
  and `appoint` take effect at the grant; only `transfer` waits for an accept.
- **Dynamic role**: a role that allows `share` or that some role appoints
  into. **Fixed role**: any other role; its positions are the root positions.
- **Arbiter**: an optional key named in the root cast. It signs numbered
  **epochs**, each listing the removals it newly covers.
- **`:under`**: the field by which an act names the seat it relies on.
- **Redelegate bit**: a grant flag that lets the holder grant further.
- **Concurrent**: two messages, neither in the other's authority past.
- **Bound**: an optional last epoch for a seat (`:until`), arbiter threads only.
- **[[round-anchor|Round anchor]]**: the message a fan-in names with `:anchor`; each
  counted act walks back to it through its own position's acts. **Round
  membership**: the positions of the counted role that exist in the anchor's
  authority past and are not emptied there (full definitions in Terminology).
- **R5**: the existing protocol-order check of SPEC-002.

How a verdict is reached:

- **Seat state.** One pure function turns a set of meta acts into seats.
  Each seat records its terminations: accepts of transfers from it, its
  resign, a revoke of it. A seat with any termination is removed. It passes
  to a successor only when its single termination is one accept.
- **Admission verdict.** SPEC-014's three-valued result, `Unknown`, `Valid` or
  `Violation`; "admitted" below means `Valid`. It uses the seat state of the
  act's *authority past*: every in-thread message reachable through its
  `:caused-by`, `:under`, `:seen` and `:anchor` links
  ([[SPEC-020-capability-seats#Terminology]]). An act is admitted when its named seat is live there
  and covers the act. A removal binds acts whose authority past contains it.
  An act that omits a removal is still admitted; this is the honest-sender
  limit. Two conflicting terminations of one seat leave its position with no
  holder at admission.
- **Counted fan-in.** An `(all …)` over an indexed role counts the round
  membership; for a fixed role that is the root positions. A position
  created after the anchor is outside the round: its acts are admitted, and
  a fan-in that cites one is `Violation`. A member position with no act in
  the fan-in is met by a removal that emptied it, cited in `:seen`.
- **Finality verdict, arbiter threads only.** `Pending` until an epoch
  covers the act, then `Final` or `Void`. The arbiter signs numbered
  epochs. Each epoch lists every admitted removal it newly covers, accepts included, in an order the arbiter chooses that respects the authority order. Finality folds the epochs: add new grants, then apply the
  listed removals one by one, skipping any that no longer applies. An act is `Final` when its seat exists in that fold and every applied removal of its seat has the act in its authority past. A removal concurrent with the act, finalised by the
  act's first covering epoch or earlier, makes the act `Void`.
- **Stolen key.** With an arbiter, two concurrent transfers of one seat are
  settled by the listed order, which can favour the thief. An occupant of the declared recovery role, not the position's old key, then reseats the position. Without an arbiter, the position
  has no holder, and the remedy is a successor thread.
- **Which verdict to use.** With an arbiter, finality decides; admission is
  provisional. Without one, admission decides.

Decisions:
[[SPEC-020-capability-seats#ADR-2000]] roles stay the unit of projection; a
role is a named capability ·
[[SPEC-020-capability-seats#ADR-2001]] grants are messages in the signed log ·
[[SPEC-020-capability-seats#ADR-2002]] chains reduce by intersection; act
subsets; a redelegate bit instead of depth ·
[[SPEC-020-capability-seats#ADR-2003]] every granted act names its authority ·
[[SPEC-020-capability-seats#ADR-2004]] two verdicts: admission from the
authority past, finality from the epoch fold ·
[[SPEC-020-capability-seats#ADR-2005]] an arbiter orders every removal
explicitly; no tie-breaks ·
[[SPEC-020-capability-seats#ADR-2006]] fan-in counts the positions live
at the round anchor ·
[[SPEC-020-capability-seats#ADR-2007]] a facet acts as its delegator's seat ·
[[SPEC-020-capability-seats#ADR-2008]] root positions are never revoked ·
[[SPEC-020-capability-seats#ADR-2009]] recovery by a declared higher role,
finalised by the arbiter ·
[[SPEC-020-capability-seats#ADR-2010]] send authority only ·
[[SPEC-020-capability-seats#ADR-2011]] without an arbiter, removal binds
honest senders only ·
[[SPEC-020-capability-seats#ADR-2012]] authority links outside R5, inside the
thread ·
[[SPEC-020-capability-seats#ADR-2013]] conflicting terminations leave no
holder at admission ·
[[SPEC-020-capability-seats#ADR-2014]] an emptied position counts as met ·
[[SPEC-020-capability-seats#ADR-2015]] liveness is claimed against named
fairness; deadlock-freedom is tested, liveness is not proved

Load-bearing:
[[SPEC-020-capability-seats#REQ-2017]] the seat-state function ·
[[SPEC-020-capability-seats#REQ-2036]] authority links ·
[[SPEC-020-capability-seats#REQ-2009]] grants never widen ·
[[SPEC-020-capability-seats#REQ-2013]] designation by `:under` ·
[[SPEC-020-capability-seats#REQ-2027]] the epoch fold ·
[[SPEC-020-capability-seats#REQ-2025]] finality verdict ·
[[SPEC-020-capability-seats#REQ-2034]] conservative extension of SPEC-014

Controls, policy and admission:
- [[SPEC-020-capability-seats#REQ-2035]] policy-bearing dialects install only when the caller opts in; the default is reject.
- [[SPEC-020-capability-seats#REQ-2009]] a grant within one role SHALL NOT widen its parent's acts, mode or bound.
- [[SPEC-020-capability-seats#REQ-2008]] a facet grant names its acts, all from the dialect's facet list.
- [[SPEC-020-capability-seats#REQ-2003]] a facet list excludes a singleton role's choice acts.
- [[SPEC-020-capability-seats#REQ-2011]] chains longer than 8 grants are rejected.
- [[SPEC-020-capability-seats#REQ-2004]] `share` and `appoint` target indexed roles only.
- [[SPEC-020-capability-seats#REQ-2005]] a dynamic role feeds occupant-counted fan-in only through an anchored round.

Controls, finality and recovery:
- [[SPEC-020-capability-seats#REQ-2012]] `:until` is rejected without an arbiter.
- [[SPEC-020-capability-seats#REQ-2020]] a transfer moves nothing until the recipient's `accept`.
- [[SPEC-020-capability-seats#REQ-2026]] an epoch lists every removal it newly covers, or it is not admitted.
- [[SPEC-020-capability-seats#REQ-2027]] listed removals apply in order; one that no longer applies is void alone.
- [[SPEC-020-capability-seats#REQ-2028]] two epochs with one number freeze finality and yield evidence.
- [[SPEC-020-capability-seats#REQ-2031]] reseat requires an arbiter and a declared, acyclic, sending recovery role.

Controls, rounds and liveness:
- [[SPEC-020-capability-seats#REQ-2046]] a fan-in names its anchor; it counts the positions present at the anchor, and a position created later is outside the round.
- [[SPEC-020-capability-seats#REQ-2047]] a removal that empties a member position stands in for its act when the fan-in holds no act of it.
- [[SPEC-020-capability-seats#REQ-2048]] a grant that yields a principal seat keeps one act at every Send step, or it is rejected.
- [[SPEC-020-capability-seats#NFR-2003]] liveness claims hold under named delivery and arbiter fairness, and no further.

The three Controls lists together exceed the Miller cap of seven. The split
into three groups is the decomposition this version makes. Splitting the spec
is recorded in Open.

Open: threshold (k-of-n) recovery, pre-rotation and fallback arbiters (owner:
HOC) · an executable model of REQ-2017 and REQ-2027 with property tests,
before implementation (owner: HOC) · Lean mechanisation of
authority-traces-to-root and finality stability (owner: HOC) · consent
co-signatures on grants (owner: HOC) · splitting policy and finality into two
specs (owner: HOC) · arbiter liveness: an arbiter that never covers an act leaves it `Pending` (owner: HOC) · round-3 review minor findings m2, m3 and m4 (retried accepts, reseat ordering, grant `Final` then removed), recorded in the review file (owner: HOC) · cbcl-bus wiring: hub as arbiter, delivery of authority
pasts and to facet holders, MLS Add/Remove from seat events (owner: cbcl-bus,
spec unwritten) · a `rotate` mode that keeps a holder's child seats when it moves its own seat to a new key (owner: HOC) · balancedness as an installation check if a future grammar adds blocking receives or recursion (owner: HOC) · the deployed REQ-608 checker's gap on the BUG-640 shape, which TEST-2053 inherits (owner: HOC) · a vacant singleton position stalls every act that cites it; no discharge exists for singletons (owner: HOC) · liveness over infinite traces in Lean, after the Rocq method (f-session-26) (owner: HOC).

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
[[SPEC-014-role-layer-endpoint-projection#REQ-614]]). Five failure modes
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
  f-conv-23, f-ocap-19).
- **FM-4 Captured seat.** A stolen key can hand its seat to the thief, and a
  lost key strands the seat. No message can repair either case today.
- **FM-5 Tie-break state resets.** Systems that settle concurrent authority
  changes with a deterministic rule over the DAG let an attacker grind or
  backdate events to win. Matrix shipped such a rule and suffered state
  resets, published as CVE-2025-49090 (f-conv-12, f-conv-14, f-conv-17,
  f-conv-18). cbcl-bus already forbids tie-breaks between concurrent MLS
  commits.
- **FM-6 Stuck round.** A position counted by a fan-in loses its seat by
  resign, revoke or cascade. No fan-in over that round can ever be `Valid`,
  so the thread never closes. A vacant singleton position stalls every act
  that cites it the same way; that case stays a limit (Open). SPEC-014 names a vacant role as a liveness gap and
  bounds nothing ([[SPEC-014-role-layer-endpoint-projection#REQ-619]]).
  Session calculi forbid leaving before the local type ends
  (f-session-27), which a stolen key never respects.

### What the literature says

The design comes from a survey of four literatures, coordinated in the
elephant theory `cap-epp-lit`. Appendix A lists every source and finding,
and each ADR cites the findings it rests on. The four main conclusions are
below.

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
   over a concurrent use is not (f-certs-28). No rule over the DAG alone
   separates a legitimate concurrent removal from a backdated one
   (f-conv-19).
4. **An arbiter supplies what the DAG cannot.** Signed epoch events from a
   designated arbiter order the non-monotone acts. Arbiter equivocation is
   provable fraud (f-conv-20, f-conv-21). This matches the cbcl-bus hub,
   which already orders MLS commits as a delivery service (f-conv-30).
5. **Liveness is a claim against a fairness assumption.** Mechanised MPST
   results keep safety, deadlock-freedom and liveness apart. They state
   liveness only under named fairness and for balanced protocols
   (f-session-23, f-session-24). The theorems cover processes that implement
   a subtype of their projection (f-session-25). Dynamic sessions fix the
   counted membership per block and let late joiners wait for the next one
   (f-session-28).

### Terminology

- **Act**: an instance of a dialect performative.
- **Meta act**: one of `grant`, `accept`, `revoke`, `resign`, `reseat`,
  `epoch` (CON-2001). Meta acts carry no protocol obligation, as SPEC-014
  already provides for meta messages.
- **Role**: a named class of behaviour declared in `:roles`. Projection
  ranges over roles exactly as in SPEC-014. A role is *singleton* or
  *indexed*.
- **Position**: a root position is one `(role, key)` binding of the root
  cast, named by its role and original key. A `share` or `appoint` grant
  creates a new position named by the grant hash.
- **Seat**: the authority to send a set of acts in one role, held by one key.
  A seat has an id, a position, a holder, a mode, an act set and a chain. It also has a redelegate flag and, when set, a bound.
  The word *seat* is coined by this spec. The session-type literature says
  a participant occupying a role (f-session-01).
- **Seat ids**:
  - `Root(position)` for a root seat;
  - `Grant(h)` for a `facet`, `share` or `appoint` grant;
  - `Moved(h)` for an accepted transfer, named by the accept;
  - `Reseated(h)` for an applied reseat.
- **Principal seat** of a position: the root seat, a `share` or `appoint`
  seat, or the `Moved` or `Reseated` seat that replaced one of them. A facet
  seat is never a principal seat.
- **Chain**: the list of seat ids from a root seat down to a seat. A `facet` or `share` seat's chain is its parent's chain plus itself. An `appoint` seat's
  chain is its appointer's chain plus itself. A `Moved` or `Reseated` seat's
  chain is the replaced seat's chain with the replaced seat swapped for
  itself.
- **Termination** of seat `X`, within a set of admitted meta acts, is one of:
  - an admitted accept of an admitted transfer grant issued under `X`;
  - a `resign` of `X`;
  - a `revoke` of `X`;
  - an admitted `reseat` naming `X`'s position, when `X` is that position's principal seat.
- **Removal**: a meta act that terminates some seat: accept, revoke, resign
  or reseat. **Monotone meta act**: `grant`.
- **Seat attributes**: a root seat has mode `transfer`, every act of its role and no bound. Its redelegate flag is `#t` when its role's policy lists `redelegate`. A `Moved` or `Reseated` seat copies the attributes of the seat
  it replaces. A granted seat takes the attributes its grant states.
- **Dynamic role**: a role that declares `share` or that an `:appoint`
  clause names.
- **Authority links** of a message: its `:caused-by`, `:under`, `:seen` and `:anchor` targets. A meta act adds its `:grant` target and hash-form `:seat`. An epoch adds its `:prev` and `:order` entries. This list is canonical; every other mention defers to it.
- **Authority past `A(m)`**: the in-thread messages reachable from `m`
  through authority links, `m` excluded.
- **Arbiter**: an OPTIONAL key named in the root cast that signs epochs.
- **Epoch chain**: the admitted epochs numbered 1, 2, … in `:prev` order.
- **Batch `B_k`**: the messages in `A(E_k)` and not in `A(E_{k-1})`, where
  `E_k` is epoch `k`. `B_1` is `A(E_1)`.
- **Covering epoch `E(m)`**: the epoch `k` whose batch contains `m`.
- **Honest sender**: a sender whose act has, in its authority past, every
  removal it has received. The protocol cannot check this property; ADR-2011
  explains why it matters.
- **Round anchor** of an occupant-counted fan-in: the message its `:anchor`
  names, or the thread root when `:anchor` is absent. **Anchor walk** of a
  counted act: follow its single protocol predecessor while that predecessor
  is an act of the same position. The walk ends at the first other message.
- **Round membership**: the positions of the counted role that are root
  positions or created by a grant in `A(anchor)`. Positions emptied in
  `A(anchor)` are excluded.
- **Emptied position**, in a set of admitted meta acts: a position whose
  every principal seat is removed in the seat state. Its terminations
  contain no accept. Resign, revoke, reseat of an ancestor and cascades
  empty a position; accepts move or contest it. **Discharge**: the removals
  that empty a member position, standing in for its act in a fan-in.
- **Delivery fairness**: every message of the thread eventually reaches the
  store of every recipient. **Arbiter fairness**: every message of an
  arbiter thread is eventually in the batch of an admitted epoch. Both are
  assumptions about the environment, never checked by the verifier.

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

**REQ-2001: Fixed is the default.**
WHEN a role declaration carries no policy clause, the system SHALL treat the
role as fixed: no grant, appointment, transfer or reseat names it.
Acceptance: a dialect written for SPEC-014 parses to `RolePolicy::fixed()`
for every role.
Trace: [[SPEC-020-capability-seats#TEST-2001]]. Failure mode: FM-1
(compatibility).

**REQ-2002: Policy is signature-bound.**
The canonical signable form of a dialect SHALL include every policy clause,
as a new canonical-form version. A policy stripped or widened in transit then
invalidates the dialect's R4 signature.
Trace: [[SPEC-020-capability-seats#TEST-2002]]. Failure mode: FM-1.

**REQ-2003: Policy names declared things.**
The installation check SHALL reject a dialect in which an `:appoint` or
`:recover-by` clause names an undeclared role. It SHALL also reject a `facet`
clause that names an act whose `:from` is not the declaring role. For a
singleton role, it SHALL reject a `facet` clause that names an act by which
that role chooses ([[SPEC-014-role-layer-endpoint-projection#REQ-606]]).
Trace: [[SPEC-020-capability-seats#TEST-2003]]. Rationale: without this rule, a facet holder and its delegator can make two conflicting choices as one seat.

**REQ-2004: Sharing and appointment target indexed roles.**
The installation check SHALL reject a dialect that declares mode `share` on
a singleton role, or an `:appoint` clause that names a singleton role.
Trace: [[SPEC-020-capability-seats#TEST-2004]]. Rationale:
[[SPEC-020-capability-seats#ADR-2007]].

**REQ-2005: Dynamic roles feed fan-in only through an anchored round.**
Consider an occupant-counted `(all …)` fan-in
([[SPEC-014-role-layer-endpoint-projection#REQ-618]]) whose predecessor role is dynamic. The installation
check SHALL walk the counted performative back through the protocol: while
its predecessor is one performative of the counted role, step to it. The
walk SHALL end at one performative of a singleton role, or at the root.
A step meets a stop when it reaches an `(all …)`, a multi-alternative
predecessor list, or a performative of another indexed role. WHEN that
happens, the check SHALL reject the dialect with `DynamicRoleInFanIn`. The auction's `reveal`, which follows the
bidder's own `commit` after the auctioneer's `open`, passes.
Trace: [[SPEC-020-capability-seats#TEST-2005]]. Rationale:
[[SPEC-020-capability-seats#ADR-2006]].

**REQ-2038: Recovery roles form no cycle and can send.**
The installation check SHALL reject a dialect whose `:recover-by` relation
has a cycle, including a role that names itself. It SHALL also reject a
`:recover-by` role whose projection has no Send step.
Trace: [[SPEC-020-capability-seats#TEST-2038]]. Rationale:
[[SPEC-020-capability-seats#ADR-2009]].

**REQ-2043: Meta-act names are reserved.**
The installation check SHALL reject a dialect that declares a performative named `grant`, `accept`, `revoke`, `resign`, `reseat` or `epoch`. It SHALL also reject a performative parameter named `under` or `seen`.
Trace: [[SPEC-020-capability-seats#TEST-2043b]].

### Cast extension

**REQ-2006: Arbiter and per-thread restriction on the root.**
The `with-roles` wrapper SHALL accept an OPTIONAL `:arbiter` key and an
OPTIONAL `:fixed` role list per [[SPEC-020-capability-seats#CON-2001]]. A
role listed in `:fixed` is fixed in that thread whatever its dialect policy.
Acceptance: the parsed `Cast` carries the arbiter key and the fixed set; a
`:fixed` entry naming an undeclared role yields `MalformedCast`.
Trace: [[SPEC-020-capability-seats#TEST-2006]].

### Authority links

**REQ-2036: Authority links are outside protocol order.**
The system SHALL compute `A(m)` over authority links. R5 `verify_causal`
SHALL continue to check `:caused-by` links only. Other authority links SHALL
NOT count as protocol predecessors under
[[SPEC-014-role-layer-endpoint-projection#REQ-616]].
Acceptance: take a protocol-valid act whose `:under` names a grant and whose
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
authority past. A consumer that admits a new seat holder SHALL make available
every message in the authority past of the meta acts that seated it.
Trace: [[SPEC-020-capability-seats#TEST-2042b]]. Rationale: SPEC-014 causal
locality assumes an endpoint holds the predecessors it cites. A late joiner
holds none of the earlier meta acts.

### Grants and chains

**REQ-2007: Grant admission requires a held seat.**
WHEN the system admits a `grant`, it SHALL require a live seat named by the grant's `:under`. Liveness is judged in the seat state of `A(grant)`. The grant's
signer SHALL hold that seat.
Trace: [[SPEC-020-capability-seats#TEST-2007]]. Failure mode: FM-2.

**REQ-2008: Grant mode and acts are permitted.**
The system SHALL reject a grant whose mode or redelegate flag the dialect
policy of its role does not permit. It SHALL also reject a grant for a role
that the root cast lists in `:fixed`. A `facet` grant SHALL carry `:acts`,
and every act in it SHALL appear in the role's `(facet …)` list.
Trace: [[SPEC-020-capability-seats#TEST-2008]].

**REQ-2009: Grants within one role never widen.**
The system SHALL NOT admit a `facet`, `share` or `transfer` grant that widens
its parent seat. Such a grant widens its parent when any of these holds:
- its act set is not a subset of the parent's act set;
- its bound is later than the parent's bound;
- its mode is stronger than the parent's, in the order `facet` < `share` <
  `transfer`.
A grant without `:until` takes its parent's bound.
Trace: [[SPEC-020-capability-seats#TEST-2009]] (prohibited action),
[[SPEC-020-capability-seats#TEST-2040]] (property). Rationale:
[[SPEC-020-capability-seats#ADR-2002]].

**REQ-2039: Appointment.**
The system SHALL admit an `appoint` grant into role `R` under a seat in role
`Q` only if `Q` declares `:appoint (… R …)`. The new seat's act set is a
subset of `R`'s acts, all of them when `:acts` is absent. Its bound SHALL NOT
be later than the appointer's bound.
Acceptance: an appointment under a seat whose role lacks the clause is
rejected with `ModeNotPermitted`. Revoking the appointer's seat removes the
appointee.
Trace: [[SPEC-020-capability-seats#TEST-2039]]. Failure mode: FM-1.

**REQ-2010: Redelegation requires the bit.**
The system SHALL reject a grant whose parent is a granted seat issued with
`:redelegate #f`.
Trace: [[SPEC-020-capability-seats#TEST-2010]].

**REQ-2011: Bounded chain length.**
The system SHALL reject a designation that resolves through a chain of more
than 8 grants.
Trace: [[SPEC-020-capability-seats#TEST-2011]],
[[SPEC-020-capability-seats#NFR-2000]]. Rationale: zcap bounds chains for the
same reason (f-certs-21).

**REQ-2012: No expiry without an arbiter.**
The system SHALL reject a grant that carries `:until` in a thread whose root
cast names no arbiter.
Trace: [[SPEC-020-capability-seats#TEST-2012]]. Rationale:
[[SPEC-020-capability-seats#ADR-2011]].

### Designation

**REQ-2013: Every act names a covering seat in its own role.**
WHEN an act's authority comes from a granted, moved or reseated seat, the act
SHALL carry `:under` naming that seat's id hash. The system SHALL evaluate
the act only against the named seat. The named seat's role SHALL equal the
act's `:from` role in the dialect.
Acceptance:
- An act that omits `:under` is checked against the seat that REQ-2015 resolves.
- An act naming a seat that does not cover it is a `Violation`. This holds
  even when another seat held by the signer covers the act.
- An act naming a seat of another role is a `Violation`.
Trace: [[SPEC-020-capability-seats#TEST-2013]] (including the confused-deputy
case). Failure mode: FM-2. Rationale: [[SPEC-020-capability-seats#ADR-2003]].

**REQ-2014: Designation resolves to a seat of this thread.**
The system SHALL return `Violation` when the hash named by `:under` is not an
admitted grant, accept or reseat of the same thread.
Trace: [[SPEC-020-capability-seats#TEST-2014]].

**REQ-2015: Root-seat designation.**
The system SHALL accept `:under (root R K)` as a designation of the root seat of position `(R, K)`. That root seat is resolved once, in the act's authority past, and never by a later state. WHEN the signer's key holds
exactly one root position in `R`, the system SHALL also accept an omitted
`:under` or `:under (root R)` for that position. WHEN it holds more than one,
the system SHALL reject both short forms.
Trace: [[SPEC-020-capability-seats#TEST-2015]]. Rationale: an ambiguous short
form re-creates the search that ADR-2003 forbids.

**REQ-2016: Signature ratifies the holder.**
The system SHALL attribute an act to a seat only if the act's `signed`
wrapper key equals the seat's holder key. The self-asserted `:sender` field
never decides attribution. This restates
[[SPEC-014-role-layer-endpoint-projection#REQ-612]] for every seat.
Trace: [[SPEC-020-capability-seats#TEST-2016]].

### Seat state

**REQ-2017: The seat-state function.**
The system SHALL compute `seat_state(root cast, S)` for a set `S` of
admitted meta acts as follows:
1. The issued seats are the root seats and one seat per admitted `facet`, `share` or `appoint` grant in `S`.
2. A seat is removed when `S` contains a termination of it.
3. A seat's successor is the `Moved` or `Reseated` seat of its termination, under two conditions. That termination is the seat's only one, and no revoke of the accepted transfer grant is in `S`. Otherwise the seat has no successor.
4. A seat is live when it is issued, not removed, and every seat in its chain
   is live.
5. A `Moved` or `Reseated` seat is issued only if the seat it replaces is issued and this seat is that seat's successor. Issuance is defined inductively along the replacement chain, so a contested seat issues no successors at any depth.
The result SHALL NOT depend on any order of `S`.
Trace: [[SPEC-020-capability-seats#TEST-2017]],
[[SPEC-020-capability-seats#TEST-2041]] (property). Failure modes: FM-1,
FM-4. Refines [[SPEC-014-role-layer-endpoint-projection#REQ-614]] and the
immutable-binding clause of
[[SPEC-014-role-layer-endpoint-projection#REQ-613]].

**REQ-2037: Conflicting terminations leave no holder at admission.**
Consider a seat with two or more terminations in `S`, at least one an accept. WHEN `S` holds such terminations, the system SHALL issue no successor for that seat.
Trace: [[SPEC-020-capability-seats#TEST-2037]]. Failure modes: FM-4, FM-5.
Rationale: [[SPEC-020-capability-seats#ADR-2013]].

**REQ-2018: Projection is unchanged.**
The system SHALL compute each role's local protocol with SPEC-014 `project`
unchanged. A facet seat's Send steps SHALL be the role's Send steps
restricted to the facet's act set.
Trace: [[SPEC-020-capability-seats#TEST-2018]]. Rationale:
[[SPEC-020-capability-seats#ADR-2000]].

**REQ-2019: How a root position changes holder.**
The principal seat of a root position SHALL change only in three ways. They are an accepted transfer, a `resign` by its holder, and a reseat applied in the epoch fold. No
`revoke` names a root seat, because a revoke names a grant hash.
Trace: [[SPEC-020-capability-seats#TEST-2019]]. Rationale:
[[SPEC-020-capability-seats#ADR-2008]].

**REQ-2020: Transfer completes on accept.**
WHEN a grant has mode `transfer`, the system SHALL leave the parent seat with
its issuer. The seat moves only when an admitted `accept` by the grant's
holder names the grant. The transfer grant itself is never a live seat and
issues nothing. This is the asynchronous form of session delegation: the
channel moves when the receiver catches it, and the other party's view is
unchanged (f-session-08, f-session-09).
Acceptance:
- Before the accept, the issuer's acts under the parent seat stay `Valid`.
- Before the accept, acts under the transfer grant are `Violation`.
- After the accept, acts under the `Moved` seat are `Valid` and the issuer's
  acts under the parent seat are `Violation`.
- After the accept, every seat issued under the parent seat is removed.
Trace: [[SPEC-020-capability-seats#TEST-2020]]. Failure mode: FM-4.

**REQ-2045: Accept admission.**
The system SHALL admit an `accept` only if all of these hold, in `A(accept)`:
- its `:grant` names an admitted `transfer` grant of the same thread;
- the accept's signer is that grant's `:to` key;
- the grant's parent seat is live, and no revoke of the grant is present.
Trace: [[SPEC-020-capability-seats#TEST-2048]]. Failure mode: FM-4.

**REQ-2040: Resign and revoke require authority.**
The system SHALL admit a `resign` only if its signer holds the named seat in
the seat state of `A(resign)`. The system SHALL admit a `revoke` of seat `G` only if its `:under` names a live seat held by its signer. That seat SHALL be in `G`'s chain before `G`.
Trace: [[SPEC-020-capability-seats#TEST-2046]],
[[SPEC-020-capability-seats#TEST-2033]]. Failure mode: FM-2.

**REQ-2021: Recipients and delivery follow seats.**
The system SHALL check a message's recipient set ([[SPEC-014-role-layer-endpoint-projection#REQ-622]]) against each addressed role's seat holders. These are the holders of live principal seats in the seat state of `A(m)`. A
role with no live principal seat requires no recipient. Facet holders are
not recipients. The delivery set of a message SHALL be its recipients plus
the holders of live facet seats under those recipients' seats.
Trace: [[SPEC-020-capability-seats#TEST-2021]]. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-615]]. Limit: a sender who
cites an older authority past can omit a newer member. That costs the member
delivery, not safety; consumers deliver by their current state.

**REQ-2032: Meta acts reach everyone affected.**
The system SHALL reject a meta act whose recipient set omits any of these
keys:
- a holder of a live principal seat in the seat state of `A(meta act)`;
- the arbiter, when the root cast names one;
- for a grant, the grant's holder;
- for an accept, revoke, resign or reseat, the holder of every seat it removes.
Trace: [[SPEC-020-capability-seats#TEST-2032]]. Rationale: every endpoint
needs membership changes in its authority past. This is the analogue of the
SPEC-014 root convention
([[SPEC-014-role-layer-endpoint-projection#ADR-603]]).

**REQ-2041: Fan-in counts round membership.**
For an occupant-counted `(all …)` fan-in over an indexed role, the system
SHALL count the positions in the round membership of REQ-2046. A
referenced act satisfies the position of its designated seat. A referenced
act of the counted performative from a position outside the round makes the
fan-in `Violation` with `PositionOutsideRound`, as
[[SPEC-014-role-layer-endpoint-projection#REQ-618]] treats a non-member.
Acceptance: a facet act satisfies its delegator's position. After a
transfer, the new holder's act satisfies the old position. One position never
counts twice.
Trace: [[SPEC-020-capability-seats#TEST-2047]]. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-618]]. Rationale:
[[SPEC-020-capability-seats#ADR-2006]].

**REQ-2046: Round anchor and membership.**
A fan-in over a dynamic role SHALL name its anchor with `:anchor`. The
anchor SHALL be an in-thread message in the fan-in's authority past. For
each referenced act of the counted performative, the system SHALL run the
anchor walk (Terminology). WHEN a walk ends at a message other than the
anchor, the fan-in SHALL be `Violation` with `MixedRounds`. The round
membership SHALL be computed from the seat state over the meta acts of
`A(anchor)` (Terminology). A fan-in with no referenced counted act is
`Valid` only when every member position is discharged. The anchor is
resolved once, from content, and never from a later state. A fan-in over a
fixed role omits `:anchor`, and its membership is the root positions.
Acceptance: with the root as anchor, the membership equals the root
positions of the role, which is the v0.4.0 behaviour.
Trace: [[SPEC-020-capability-seats#TEST-2051]]. Failure mode: FM-1. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-618]]. Rationale:
[[SPEC-020-capability-seats#ADR-2006]], [[SPEC-020-capability-seats#ADR-2003]].

**REQ-2047: An emptied position counts as met.**
Consider a member position with no act of its own, for this round, in the
fan-in's authority past. The system SHALL count it as met when the fan-in's
authority past empties it (Terminology). WHEN an act of that position for
this round is in the fan-in's authority past, the removals SHALL NOT stand
in for it. A contested position (REQ-2037) is a member that only an act
under one of its issued seats, or a later discharge, satisfies. An accepted
transfer empties nothing: the successor seat acts for the position.
Acceptance: a fan-in that references every other position's act and cites
the resign in `:seen` is `Valid`. Without the resign, no fan-in over that
round is `Valid`. A revoke of a share's parent discharges the share.
Limit: a collector that omits a position's act and cites its removal is
the honest-sender limit of ADR-2011; the omitted act stays in the log.
Trace: [[SPEC-020-capability-seats#TEST-2052]],
[[SPEC-020-capability-seats#TEST-2054]]. Failure mode: FM-6. Rationale:
[[SPEC-020-capability-seats#ADR-2014]].

**REQ-2048: A principal seat can meet its projection.**
A *Send step* of a role is a maximal set of its Send performatives
([[SPEC-014-role-layer-endpoint-projection#CON-602]]) that are alternatives of one choice
([[SPEC-014-role-layer-endpoint-projection#REQ-603]]). A Send performative in no choice is a step by itself.
Consider a `share`, `appoint` or `transfer` grant. At admission, the system
SHALL check the grant's act set against the Send steps of the granted role. The
act set SHALL keep at least one performative of every Send step. Otherwise
it SHALL reject the grant with `UnliveGrant`. A `facet` grant is exempt,
because its delegator's seat covers the position. For a `share` or
`appoint`, the system SHALL also run
[[SPEC-014-role-layer-endpoint-projection#REQ-608]]. Its cast is the root cast, the live principal
positions of `A(grant)`, and the new position. A failure is
`NotCausallyLocal`, carrying the `R6Violation`.
Trace: [[SPEC-020-capability-seats#TEST-2053]]. Failure mode: FM-6. Refines
[[SPEC-014-role-layer-endpoint-projection#REQ-608]].
Rationale: [[SPEC-020-capability-seats#ADR-2015]] (f-session-25).

### Admission verdict

**REQ-2022: Admission verdict.**
`verify_with_capabilities` SHALL return an admission verdict for every
message as a function of the message and `A(m)` only. For an act, the verdict
SHALL be the SPEC-014 role-local verdict met with these checks, against `seat_state(root cast, admitted meta acts of A(m))`:
- the designated seat is live, held by the signer, of the act's role, and
  covers the act;
- the recipient set satisfies REQ-2021.
For a meta act, the verdict SHALL apply the meta act's own admission REQs.
Trace: [[SPEC-020-capability-seats#TEST-2022]],
[[SPEC-020-capability-seats#TEST-2041]]. Rationale:
[[SPEC-020-capability-seats#ADR-2004]].

**REQ-2023: Removals in the authority past bind.**
WHEN `A(m)` contains a removal of `m`'s designated seat or of a link of its
chain, the admission verdict SHALL be `Violation`. A reseat counts as a removal at admission like an accept. Finality decides in arbiter threads, the only threads where a reseat is admitted.
Trace: [[SPEC-020-capability-seats#TEST-2023]]. Failure mode: FM-3 (honest
senders).

**REQ-2024: Admission monotonicity.**
The admission verdict SHALL be monotone in the valid-is-sticky order of
[[SPEC-014-role-layer-endpoint-projection#REQ-620]]. Store growth never
changes `Valid`. The verdict is permanent once `A(m)` is present.
Trace: [[SPEC-020-capability-seats#TEST-2024]].

### Finality verdict

**REQ-2026: Epochs come from the arbiter in sequence and list every removal.**
The system SHALL admit an `epoch` only if all of these hold:
- the arbiter key signs it;
- its number is 1 and its `:prev` is `none`, or its `:prev` names the
  admitted epoch numbered one lower;
- that previous epoch is in its authority past;
- its `:order` lists every removal in its batch whose admission verdict is `Valid`, exactly once, and nothing else;
- its `:order` never lists a removal before another entry in that removal's authority past.
Trace: [[SPEC-020-capability-seats#TEST-2026]]. Rationale: an arbiter that
omits a removal can otherwise censor it.

**REQ-2027: The epoch fold.**
The system SHALL compute the finalised state `F_k` from `F_{k-1}`, starting
from the root seats as `F_0`, in two steps:
1. Walk the batch `B_k` once. Take grants in authority order and removals
   in `:order` order, merged so that every message follows its authority
   links. A grant is added if it passes REQ-2007 through REQ-2012 with
   liveness judged in the current state.
2. A removal is applied if its own admission verdict is `Valid` and it passes
   its admission REQ (REQ-2031, REQ-2040, REQ-2045) with liveness judged in
   the current state. Otherwise it is marked void. Applying an accept or
   reseat removes the replaced seat and issues its successor. Applying a
   revoke or resign removes the named seat.
3. A seat whose bound is an epoch numbered below `k` is removed at the start
   of epoch `k`.
Removal cascades to every seat whose chain contains a removed seat. Accepts
and reseats apply one at a time, so a later accept of a removed seat is void.
Acceptance: for two accepts of transfers of one seat listed in one epoch,
the first applies and the second is void.
Trace: [[SPEC-020-capability-seats#TEST-2027]]. Failure mode: FM-5.
Rationale: [[SPEC-020-capability-seats#ADR-2005]].

**REQ-2025: Finality verdict.**
WHEN the root cast names an arbiter, `verify_with_capabilities` SHALL return
a finality verdict for each message `m`. For an act with `E(m) = k`:
- `Pending` while no epoch covers `m`;
- `Void` when the admission verdict's R5, role, signature or recipient checks failed, or when the designated seat does not cover the act;
- `Void` when the designated seat is not issued in `F_k`;
- `Void` when an entry applied in epochs 1 to `k` removed the seat or a chain link, and that entry's authority past lacks `m`;
- `Void` when the seat's bound is an epoch numbered below `k`;
- for a fan-in, `Void(EntryVoid)` when a referenced counted act is `Void`
  in epochs 1 to `k`. The same when a discharge its count relied on is
  `Void`. A member seat whose bound passed before `k` counts as discharged;
- `Final` otherwise.
A grant is `Final` when step 1 of its covering epoch adds it, and `Void`
otherwise. A removal is `Final` when applied and `Void` when marked void.
Without equivocation evidence, the verdict is a function of `m` and the
authority past of `E(m)` only.
Trace: [[SPEC-020-capability-seats#TEST-2025]]. Failure mode: FM-3.
Rationale: [[SPEC-020-capability-seats#ADR-2004]],
[[SPEC-020-capability-seats#ADR-2005]].

**REQ-2028: Arbiter equivocation freezes finality.**
WHEN the store holds two admitted epochs with one number `n`, the system
SHALL return `Frozen` as the finality verdict. This applies to every message
that no epoch below `n` covers. The system SHALL return the pair as
`EquivocationEvidence`.
Trace: [[SPEC-020-capability-seats#TEST-2028]],
[[SPEC-020-capability-seats#OBS-2001]]. Failure mode: FM-5.

**REQ-2029: No finality without an arbiter.**
WHEN the root cast names no arbiter, the system SHALL return the finality
verdict `NotApplicable` for every message.
Trace: [[SPEC-020-capability-seats#TEST-2029]]. Rationale:
[[SPEC-020-capability-seats#ADR-2011]].

**REQ-2030: Finality stability.**
The system SHALL NOT change a finality verdict of `Final` or `Void` while the
store holds no equivocation evidence. With equivocation evidence, a verdict that depends on an epoch at or above the equivocated number SHALL become `Frozen`. A `Void` from failed admission checks never changes. No other change SHALL occur.
Trace: [[SPEC-020-capability-seats#TEST-2042]] (property),
[[SPEC-020-capability-seats#TEST-2030]] (late equivocation).

### Recovery

**REQ-2031: Reseat by a declared role, with an arbiter.**
The system SHALL admit a `reseat` of a root position in role `R` only if all
of these hold:
- the root cast names an arbiter;
- the dialect declares `(R … :recover-by Q)`;
- the signer holds a live principal seat of a root position in `Q`;
- the reseat names the root position it replaces by role and original key.
At admission the reseat is a termination of the position's principal seat (REQ-2017). In the epoch fold it removes that seat and issues a `Reseated` seat held by the reseat's `:to` key. A reseat of a position with no principal seat in the current state is void.
Trace: [[SPEC-020-capability-seats#TEST-2031]]. Failure mode: FM-4.
Rationale: [[SPEC-020-capability-seats#ADR-2009]].

### Compatibility and enablement

**REQ-2034: Conservative extension.**
Consider a dialect with no policy and a root cast with no arbiter. Consider a message that is not a meta act, carries no `:under` or `:seen`, and links only within its thread. WHEN all hold, the
system SHALL return the SPEC-014 `verify_causal_for_role` verdict as the
admission verdict.
Trace: [[SPEC-020-capability-seats#TEST-2034]] (differential, the full
SPEC-014 fixture corpus). This protects SPEC-014's Lean correspondence.

**REQ-2035: Policy-bearing dialects are opt-in at installation.**
The installer SHALL reject a dialect that carries any policy clause unless
the caller passes `CapabilityPolicy::Accept`. The default SHALL be
`CapabilityPolicy::Reject`.
Acceptance: with the default, a policy-bearing dialect fails installation
with `CapViolation::CapabilitiesDisabled`; with `Accept`, it installs.
Trace: [[SPEC-020-capability-seats#TEST-2035]]. Default rationale: consumers
such as cbcl-bus need an arbiter, authority-past delivery and MLS wiring
before seats change membership. Rejecting by default keeps every deployed
consumer on SPEC-014 behaviour until it opts in. Setting the option back to
`Reject` is the rollback; it stops new policy-bearing dialects from
installing.

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
only, as [[SPEC-014-role-layer-endpoint-projection#NFR-601]] requires.
Trace: [[SPEC-020-capability-seats#TEST-2041]].

**NFR-2002: no_std parity and no new dependencies.**
The capability layer SHALL compile under the `no_std`+`alloc` configuration
of `cbcl-core` and SHALL add no external crate dependency.
Trace: CI matrix; `Cargo.toml` diff review.

**NFR-2003: Liveness under named fairness.**
The seat layer SHALL satisfy three claims, each under the named assumption:
- Under delivery fairness, a message leaves `Unknown` once its authority
  past, and its anchor's authority past, are present. No verdict waits on a
  message outside those two sets.
- Under delivery fairness, a round in which every member position has an
  act or is emptied admits a `Valid` fan-in.
- Under delivery and arbiter fairness, every `Pending` finality becomes
  `Final`, `Void` or `Frozen`.
Liveness beyond these claims is not proved. Balancedness (f-session-24) does
not bear on them: no CBCL endpoint blocks on a receive, so a role absent
from a branch waits on nothing.
Trace: [[SPEC-020-capability-seats#TEST-2054]],
[[SPEC-020-capability-seats#TEST-2055]]. Failure mode: FM-6. Rationale:
[[SPEC-020-capability-seats#ADR-2015]].

## Observability

**OBS-2000: Typed reasons.**
Every admission rejection SHALL carry exactly one `CapViolation` variant.
Every finality `Void` SHALL carry exactly one `VoidReason` variant. A
consumer can count and alert on both. The pure core keeps no counters.
Trace: [[SPEC-020-capability-seats#TEST-2044]].

**OBS-2001: Equivocation evidence.**
WHEN REQ-2028 fires, the verifier SHALL return both epoch hashes as an
`EquivocationEvidence` value that a consumer can store and show to others.
Trace: [[SPEC-020-capability-seats#TEST-2028]].

## Architecture Decisions

**ADR-2000: Roles stay the unit of projection; a role is a named capability.**
Decision. Projection ranges over roles exactly as in SPEC-014. Authority to
act in a role is a seat. A role is the named, addressable template from which
seats are issued.
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
Decision. Within one role, a grant narrows its parent along three axes: act
set (subset), mode (`facet` < `share` < `transfer`), and bound (`:until`
epoch, no later, inherited when absent). A boolean `:redelegate` replaces a
depth limit. An appointment starts a new role's act set, bounded by the
appointer's bound.
Evidence. Session delegation is linear: the delegator gives up the endpoint
and there is no shared use (f-session-09). `transfer` is that classical case;
`share` and `facet` are co-occupancy, which only dynamic multirole sessions
supply (f-session-01). SPKI reduces a chain by intersecting each link's authority and
validity (f-certs-01). It keeps the intersection syntactic so verification
needs no application semantics (f-certs-02). UCAN, zcap and Meadowcap narrow
by subset or prefix (f-certs-10, f-certs-22, f-conv-32). SPKI rejected depth
control because depth bounds neither tree width nor proxying (f-certs-03,
f-certs-04). Filtering forwarders attenuate by message kind (f-ocap-16).
Rejected. *Caveat predicates* over act arguments: they need
application-specific reduction software (f-certs-02, f-certs-11). Predicates
remain an Open extension.
Limit. A holder can always proxy for another party or mint a key it
controls (f-certs-03, f-certs-04). Narrowing therefore bounds what a seat
authorises and who answers for it. It does not confine the holder
(f-ocap-24).

**ADR-2003: Every granted act names its authority.**
Decision. An act made under a granted, moved or reseated seat names that
seat's id in `:under`. The verifier checks the act against that seat only
and never searches. The seat's role has to match the act's role. A short
root form is allowed only when it names exactly one position.
Evidence. The literature agrees on this point. Designation travels with
authority (f-ocap-01, f-ocap-03, f-ocap-04). A deputy with two authorities
has to say which one it uses (f-ocap-02). Identity lookups re-create access
lists (f-ocap-06). The prover supplies the chain (f-certs-08, f-certs-14,
f-certs-21, f-certs-23). Local-first verification cites the grant event id
(f-conv-24).
Rejected. *Ambient search* for any seat the signer holds: seven findings
oppose it and none support it.
Consequence. Root-seat acts of single-position keys need no change, which
keeps SPEC-014 traces valid (REQ-2015, REQ-2034).

**ADR-2004: Two verdicts: admission from the authority past, finality from
the epoch fold.**
Decision. The *admission* verdict of `m` depends on `A(m)`. The *finality*
verdict of `m` depends on the epoch fold through `E(m)`, which is a function
of the authority past of `E(m)`. Both are stable under an honest arbiter, and
every replica agrees on both. Finality never consults admission's
no-holder rule.
Evidence. Eventually consistent access control splits into an immutable
verdict from the causal past and a verdict over concurrent events
(f-conv-22, f-conv-24, f-conv-09, f-conv-10). The concurrent verdict is the
one that defeats backdating (f-conv-23). Evaluating it over "all concurrent
events seen so far" is non-monotone and replica-dependent
(f-conv-25, f-certs-19). Anchoring it to the covering epoch fixes the set of
events it considers (f-conv-20).
Rejected. *Causal revocation alone*: it binds only honest senders
(f-conv-11, f-ocap-19, f-conv-07). *Verdict on learning of a revocation*
(UCAN, Biscuit): replicas disagree until all have learned it (f-certs-19,
f-certs-25). *Strong removal over concurrent events* (p2panda): the verdict
changes as late events arrive, and a backdater steers it (f-conv-06,
f-conv-18). *Finality gated on admission*: a thief's conflicting transfers in an act's authority past then void honest acts for good. That is the freeze ADR-2005 rejects.
Consequence. With an arbiter, consumers act on finality and treat admission
as provisional. ERA calls this mixed consistency (f-conv-21).

**ADR-2005: An arbiter orders every removal explicitly; no tie-breaks.**
Decision. A root cast can name one arbiter key. The arbiter signs numbered
epochs that chain by `:prev`. Each epoch lists every removal in its batch,
in an order the arbiter chooses. Entries apply in that order; an entry that
no longer applies is void alone. No rule over the DAG picks winners.
Evidence. ERA introduces finality epochs for this problem and shows that
arbiter equivocation is provable (f-conv-20). A creator or hub can act as
arbiter (f-conv-21). Only non-confluent operations need coordination
(f-conv-26). MLS already relies on a delivery service to order commits
(f-conv-29, f-conv-30). A server-issued downgrade lease plays the same part in
Keybase (f-certs-29).
Rejected. *Deterministic tie-breaks* (power, timestamp, hash, seniority):
they are gameable by grinding or backdating, and they produced Matrix state
resets (f-conv-12, f-conv-14, f-conv-17, f-conv-18). ERA itself sorts within
an epoch by such data; the explicit `:order` list replaces that sort.
*Freeze on conflict*: a backdater can force a freeze or steer which side
survives (f-conv-18). *Unlisted removals*: they let an arbiter censor a revoke.
Limit. The arbiter chooses the order, so it can favour one side, such as a
thief's transfer. Recovery (ADR-2009) is the remedy. A lost or compromised
arbiter key ends finality for the thread; the remedy is a successor thread.
Fallback arbiters (f-conv-20) remain Open.

**ADR-2006: Fan-in counts the positions live at the round anchor.**
Decision. An occupant-counted `(all …)` counts the positions of its role
present in the round anchor's authority past and not emptied there. The
fan-in names its anchor, and each counted act walks back to it through its
own position's acts. A dynamic role feeds fan-in only when that walk is
single-valued at installation.
Evidence. Dynamic Multirole Session Types makes send polls and receive
polls agree by locking the registry around each block with a two-phase
commit. Late joiners wait for the next block (f-session-02, f-session-28).
The registry is one synchronous object (f-session-29). In CBCL the opener's
authority past is that lock: one content-addressed message fixes the set
for every verifier, with no barrier. Recipients are explicit in every
message (REQ-2021), so the receive poll is already written down.
Rejected. *Root positions only* (v0.4.0): sound and needless; it excluded
every shared position from every count. *Count over `A(fan-in message)`*:
the collector controls the set. *Count over the finalised membership*: no
admission without an arbiter. *Infer the anchor as the counted acts'
common predecessor*: undefined when each occupant cites its own earlier
act. The auction's `reveal` cites its `commit` that way. Undefined too when every
member is discharged. Naming it follows ADR-2003.
Consequence. A position created after the anchor is outside the round; its
acts are admitted, and a later anchor counts it. Facet and moved seats act
for positions that exist already, so they count. The opener chooses its past and can
delay seeing a grant, never un-see one; that is the honest-sender limit of
ADR-2011, visible in the log. The SPEC-014 per-occupant locality check
([[SPEC-014-role-layer-endpoint-projection#REQ-608]]) runs for each new
position at grant admission (REQ-2048). v0.4.0 needed no such check, since
no granted position ever appeared in a fan-in reference. cbcl-bus can refuse to relay an
opener that omits a grant the hub delivered to that sender; that is relay
policy, outside this spec.

**ADR-2007: A facet acts as its delegator's seat.**
Decision. A facet grant lets its holder send a subset of the role's acts as
the delegator's seat. It adds no recipient and no position. Messages
addressed to the delegator's seat are also delivered to the facet holder, so
the holder has the predecessors its acts cite. A facet never covers a
singleton role's choice acts (REQ-2003).
Evidence. Internal delegation lets a deputy act as the principal while the
principal waits (f-session-19). A filtering forwarder attenuates by message
kind without creating a new principal (f-ocap-16). Message-level privilege
annotations check the role an act is sent in (f-session-15). Session
delegation abstracts a hand-over away from the other party's type, so the
counterpart sees one position whoever acts in it (f-session-08).
Consequence. Singleton routing and position counting are unchanged by
facets. Delivery widens, which consumers implement (Open).

**ADR-2008: Root positions are never revoked.**
Decision. No `revoke` reaches a root position. Its principal seat changes
only by accepted transfer, by `resign`, or by `reseat`. To eject a root
occupant otherwise, open a successor thread with a new root cast.
Evidence. Matrix made room creators immutable with unlimited power after
mutable creators led to takeovers and resets. It replaces a rogue creator
only by upgrading to a new room (f-conv-15, f-conv-16). Redell revokes
wholesale by changing the object identifier (f-ocap-12). Miller advises
respawning from a few durable capabilities instead of repairing broken state
(f-ocap-21).
Rejected. *Revocable root seats*: two root occupants who remove each other recreate the duelling-admins problem (f-conv-01, f-conv-07).
Consequence. A transfer or reseat removes every seat issued under the old seat, appointments included. The new holder re-issues what it wants to keep.

**ADR-2009: Recovery by a declared higher role, finalised by the arbiter.**
Decision. A dialect can declare `:recover-by Q` on role `R`, with no cycle in
that relation and with `Q` able to send. A root occupant of `Q` can then
reseat a position of `R` to a new key. A reseat takes effect only in the
epoch fold, so it needs an arbiter.
Evidence. A parent-team admin manages subteam roles in Keybase, and only root
owners manage owners (f-certs-30). A delegated KERI identifier recovers
through its delegator after key compromise; a non-delegated one cannot
recover (f-certs-33). KERI lets a recovery rotation supersede ordinary events
but not another rotation (f-certs-32). The acyclic `:recover-by` relation
plays the part of that ordering.
Rejected for v1. *Quorum reseat* (f-certs-07): threshold subjects need
multi-signature acts this spec does not define. *Pre-rotation* (f-certs-31)
needs a key-event log outside CBCL. Both remain Open. *No recovery*: without
it, a stolen key keeps the seat for good.
Consequence. Any single root occupant of `Q` can reseat `R`. Dialect authors
choose `Q` with that power in mind. A role at the top of the relation has no
recovery; its remedy is a successor thread (ADR-2008). A receive-only role
cannot be `Q`, because it never signs anything that ratifies it.

**ADR-2010: Send authority only; confidentiality stays outside CBCL.**
Decision. Seats govern what a key can send and the addressing of sends.
Whether a key can read content is decided by the encryption group, such as
MLS in cbcl-bus, and by history policy.
Evidence. Write revocation cannot remove read access already granted. Keyhive
separates pull, read and write effects (f-conv-03). Group key agreement under
concurrency is its own protocol (f-conv-04, f-conv-05, f-conv-29).
Rejected. *One mechanism for both*: it is sound in a static type discipline
(f-session-11) but cannot remove keys already distributed.

**ADR-2011: Without an arbiter, removal binds honest senders only.**
Decision. A thread without an arbiter keeps every monotone feature: share,
facet, appoint, redelegate. Its removals take effect only through the
admission verdict. They bind every act whose authority past contains them.
`:until` and `reseat` are unavailable.
Evidence. A causal-past check cannot stop a sender who omits the removal from
its authority past (f-conv-11, f-ocap-19). Clock-based expiry makes the
verdict depend on the verifier's clock (f-certs-12). Without a trusted
platform, a reducing message that is not delivered fails unsafe (f-ocap-18).
Consequence. Consumers MUST treat arbiter-less removal as advisory against
an adversary. The strong remedy without an arbiter is a successor thread.

**ADR-2012: Authority links sit outside R5 protocol order, inside the
thread.**
Decision. `:under`, `:seen` and meta-act targets are links in the authority
past that R5 does not check. They resolve only to messages of the same
thread. A sender SHOULD list in `:seen` every removal it has received and not yet cited.
Evidence. R5 rejects any `:caused-by` link to a performative its protocol
does not name ([[SPEC-014-role-layer-endpoint-projection#REQ-616]]), and meta
acts are not dialect performatives. A use in Keybase embeds a Merkle root
that contains the grant, separate from its content (f-certs-28). A UCAN
invocation carries its proof chain beside its arguments (f-certs-14).
Rejected. *Meta acts as protocol predecessors*: every dialect protocol then
needs clauses for meta acts, which changes R5 and the Lean model.
*Cross-thread links*: with them, a removal in one thread removes a seat in another.

**ADR-2013: Conflicting terminations leave no holder at admission.**
Decision. When one authority past holds two terminations of one seat and at
least one is an accept, the seat has no successor in that past. With an
arbiter, finality decides by listed order instead (ADR-2004).
Evidence. No rule over the DAG separates the legitimate move from the
backdated one (f-conv-19), and tie-breaks are excluded (ADR-2005). p2panda
also refuses to pick a side when managers remove each other (f-conv-07).
Limit. Without an arbiter, a thief holding the old key can contest a
rotation and leave the position empty. The remedy is a successor thread,
consistent with ADR-2011.

**ADR-2014: An emptied position counts as met.**
Decision. The removals that empty a member position stand in for its act.
The fan-in's authority past holds them and no act of that position for the
round. Accepted transfers and reseats keep the position, and the
successor acts. Expiry empties a position in the finality fold only.
Evidence. Dynamic Multirole Session Types lets a participant leave only when
its local type is `end` or at `unlock` (f-session-27). Otherwise a counting
participant waits for ever. A removal in CBCL cannot wait: a revoke answers
a stolen key (FM-4). Occupant-counted fan-in is the one R5 construct that
waits on several positions at once. A single citation of a vacant
singleton waits too, and stays a limit (Open).
Rejected. *Leave only at a safe point*: a thief holds the key, and no
protocol state is safe. *Obligations pass to the delegator*: the parent
then speaks for the child, the ambient authority FM-2 removes. *Only
resign and revoke of the seat itself*: a revoked parent empties every share
under it by cascade, the commonest removal path. *Require the removal to
hold the anchor*: a removal concurrent with the opener then sticks the
round again.
Consequence. A collector that omits a position's act and cites its removal
is within ADR-2011's honest-sender limit. The act stays in the log, and a
later fan-in that holds it is `Violation`. A contested position stays a
member, so a stolen key cannot empty a round by double transfer. The
deadlock-freedom test TEST-2054 rests on this rule.

**ADR-2015: Liveness is claimed against named fairness; deadlock-freedom
is tested, liveness is not proved.**
Decision. NFR-2003 names two fairness assumptions and three liveness
claims. The core suite tests deadlock-freedom over finite fair schedules
(TEST-2054). Liveness over infinite traces is Open.
Evidence. The mechanised MPST result separates safety, deadlock-freedom and
liveness, defines liveness only under a fairness assumption, and needs
balanced global types (f-session-23, f-session-24). It covers environments
associated by subtyping, which is how facets and narrowed positions relate
to the projection (f-session-25). The liveness proof is about 14K lines of
Rocq for a synchronous, static system (f-session-26). DMst, which adds
participants by protocol call, defines liveness as no stuck participant and
notes that only receives get stuck (f-session-31).
Rejected. *No liveness statement*: SPEC-014 REQ-619 names a vacant role as
liveness and bounds nothing. *Mechanised liveness now*: out of proportion
for a draft whose seat functions have no executable model yet.
Consequence. Balancedness guards a process that blocks on a receive; no
CBCL endpoint does, so a v1 protocol needs no such check. It returns as an
installation check if a future grammar adds blocking receives or recursion
(Open). REQ-2048 is the subtyping condition, stated per grant.

## Contracts

### CON-2000: Role policy grammar

Input: the SExpr AST of the dialect, after the existing reader and R1–R3.
This extends [[SPEC-014-role-layer-endpoint-projection#CON-600]]. A SPEC-014
`role-decl` remains valid and means a fixed role.

```
roles-clause  := "(" ":roles" "(" role-decl+ ")" ")"
role-decl     := symbol                              ; singleton, fixed (SPEC-014)
               | "(" "*" symbol policy* ")"          ; indexed (SPEC-014 when no policy)
               | "(" symbol policy+ ")"              ; singleton with policy
policy        := ":delegate" "(" mode+ ")"
               | ":appoint" "(" symbol+ ")"          ; indexed roles this role appoints into
               | ":recover-by" symbol                ; role whose root occupants reseat this one
mode          := "share" | "transfer" | "redelegate"
               | "(" "facet" symbol+ ")"             ; acts a facet of this role can carry
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
                     [":dialect" hash] [":arbiter" key] [":fixed" "(" symbol+ ")"]
                     signed-form ")"

meta-act      := grant | accept | revoke | resign | reseat | epoch
grant         := "(" "grant" recipients ":role" symbol ":to" key
                     ":mode" ("facet" | "share" | "transfer" | "appoint")
                     [":acts" "(" symbol+ ")"] [":redelegate" bool]
                     [":until" "(" "epoch" nat ")"]
                     ":under" designation thread-attrs ")"
accept        := "(" "accept" recipients ":grant" hash thread-attrs ")"
revoke        := "(" "revoke" recipients ":grant" hash ":under" designation thread-attrs ")"
resign        := "(" "resign" recipients ":seat" designation thread-attrs ")"
reseat        := "(" "reseat" recipients ":role" symbol ":replaces" key ":to" key
                     ":under" designation thread-attrs ")"
epoch         := "(" "epoch" recipients ":n" nat ":prev" (hash | "none")
                     ":order" "(" hash* ")" thread-attrs ")"
designation   := hash                                ; a grant, accept or reseat hash
               | "(" "root" symbol [key] ")"         ; a root position; key REQUIRED when ambiguous
thread-attrs  := ":caused-by" causes [":seen" "(" hash+ ")"] ":thread" string ":sender" key
act-authority := [":under" designation] [":seen" "(" hash+ ")"] [":anchor" hash]   ; on a dialect act
```

Each bracketed element has one fixed position, shown above. That order is
the canonical form for hashing, so each value has exactly one serialisation.
`:seen` appears once per message: in `thread-attrs` on a meta act, and in
`act-authority` on a dialect act, placed after `:caused-by`. `:anchor` appears
only on an occupant-counted fan-in over a dynamic role (REQ-2046). `recipients`,
`hash`, `key`, `causes` and `string` are the SPEC-014 and R5 productions.
`nat` is a decimal numeral without sign. `:acts` omitted means the parent seat's act set, or all of the role's acts for `appoint`. A facet grant never omits it (REQ-2008). `:redelegate` omitted means `#f`. `:replaces`
names the original root key of the position. A revoke's `:under` names the
upstream seat its signer uses (REQ-2040).
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
(fuzz, round-trip oracle).

### CON-2002: Rust API surface

```rust
// role.rs (extended)
pub enum Mode { Facet, Share, Transfer, Appoint }        // narrowing order: Facet < Share < Transfer
pub struct RolePolicy {
    pub modes: BTreeSet<Mode>,
    pub redelegate: bool,
    pub facet_acts: BTreeSet<String>,
    pub appoint: BTreeSet<String>,
    pub recover_by: Option<String>,
}
impl RolePolicy { pub fn fixed() -> Self; }
pub struct RoleDecl { pub name: String, pub cardinality: RoleCardinality, pub policy: RolePolicy }
pub struct Cast {                                       // SPEC-014 fields kept
    pub singleton: BTreeMap<String, AgentKey>,
    pub indexed: BTreeMap<String, BTreeSet<AgentKey>>,
    pub dialect_pin: Option<String>,
    pub arbiter: Option<AgentKey>,
    pub fixed: BTreeSet<String>,
}

// capability.rs (new)
pub enum Position { Root { role: String, root_key: AgentKey }, Granted(ContentHash) }
pub enum SeatId { Root(Position), Grant(ContentHash), Moved(ContentHash), Reseated(ContentHash) }
pub enum ActSet { All, Only(BTreeSet<String>) }
pub struct Seat {
    pub id: SeatId, pub position: Position, pub holder: AgentKey, pub mode: Mode,
    pub acts: ActSet, pub redelegate: bool, pub until: Option<u64>,
    pub chain: Vec<SeatId>,                              // principal seat first, this seat last
}
pub struct SeatState { /* issued, removed, successors, live — BTreeMap-backed */ }
pub enum CapabilityPolicy { Reject, Accept }            // installer option, default Reject
pub enum Finality { NotApplicable, Pending, Final, Void(VoidReason), Frozen }
pub enum VoidReason { CheckFailed, SeatNotIssued, SeatRemoved, BoundPassed, EntryVoid, GrantRejected }
pub struct CapVerdict { pub admission: VerificationResult, pub finality: Finality }
pub struct EquivocationEvidence { pub first: ContentHash, pub second: ContentHash }

pub fn authority_past<S: MessageStore>(msg: &Message, thread: &ThreadId, store: &S)
    -> Result<AuthorityPast, Unresolved>;
pub fn seat_state(d: &Dialect, root: &Cast, meta_acts: &BTreeSet<ContentHash>, store: &impl MessageStore)
    -> SeatState;
pub fn anchor_walk<S: MessageStore>(act: &Message, d: &Dialect, root: &ContentHash, thread: &ThreadId, store: &S)
    -> Result<ContentHash, Unresolved>;                   // ends at the root hash or another position's message
pub fn round_membership(d: &Dialect, root: &Cast, anchor_past: &AuthorityPast, role: &str, store: &impl MessageStore)
    -> BTreeSet<Position>;                                // members minus emptied positions
pub fn send_steps(d: &Dialect, role: &str) -> Vec<BTreeSet<String>>;   // REQ-2048
pub fn epoch_fold(d: &Dialect, root: &Cast, epochs: &[ContentHash], store: &impl MessageStore)
    -> Result<Vec<SeatState>, EquivocationEvidence>;
pub fn verify_with_capabilities<S: MessageStore>(
    msg: &Message, d: &Dialect, root_cast: &Cast, store: &S,
    thread: &ThreadId, root: &ContentHash,
) -> CapVerdict;
```

`verify_with_capabilities` returns the admission verdict of REQ-2022 and the
finality verdict of REQ-2025. All functions are pure given their arguments;
store access is read-only through the existing `MessageStore` trait.
Implements: [[SPEC-020-capability-seats#REQ-2007]] through
[[SPEC-020-capability-seats#REQ-2048]] except the grammar and consumer REQs.
Verified by: [[SPEC-020-capability-seats#TEST-2007]] through
[[SPEC-020-capability-seats#TEST-2055]].

### CON-2003: Capability error model

`CapViolation` SHALL be an enum with one variant per rejecting REQ. Grammar
and cast errors reuse the SPEC-014 `R6Violation` variants `MalformedCast` and
`UnknownRole`
([[SPEC-014-role-layer-endpoint-projection#CON-603]]).

| Variant | Rejecting REQ |
|---|---|
| `MalformedPolicy` | CON-2000 grammar |
| `PolicyNamesUnknownRole` | REQ-2003 |
| `FacetActNotInRole` | REQ-2003 |
| `FacetOverChoice` | REQ-2003 |
| `ShareOnSingleton` | REQ-2004 |
| `DynamicRoleInFanIn` | REQ-2005 |
| `MixedRounds` | REQ-2046 |
| `PositionOutsideRound` | REQ-2041 |
| `RecoveryRoleInvalid` | REQ-2038 |
| `ReservedName` | REQ-2043 |
| `MalformedMetaAct` | CON-2001 grammar |
| `CrossThreadLink` | REQ-2044 |
| `IssuerLacksSeat` | REQ-2007 |
| `ModeNotPermitted` | REQ-2008, REQ-2039 |
| `FacetActNotPermitted` | REQ-2008 |
| `WideningGrant` | REQ-2009, REQ-2039 |
| `RedelegateNotPermitted` | REQ-2010 |
| `ChainTooLong` | REQ-2011 |
| `UnliveGrant` | REQ-2048 |
| `NotCausallyLocal` | REQ-2048 (carries the `R6Violation`) |
| `UntilWithoutArbiter` | REQ-2012 |
| `ActNotCovered` | REQ-2013 |
| `SeatRoleMismatch` | REQ-2013 |
| `NotASeat` | REQ-2014 |
| `AmbiguousRoot` | REQ-2015 |
| `HolderMismatch` | REQ-2016 |
| `SeatNotLive` | REQ-2017, REQ-2023, REQ-2037 |
| `TransferNotAccepted` | REQ-2020 |
| `LacksAuthorityToRemove` | REQ-2040, REQ-2045 |
| `RecipientMismatch` | REQ-2021 |
| `MetaActRecipientMismatch` | REQ-2032 |
| `EpochInvalid` | REQ-2026 |
| `ReseatNotPermitted` | REQ-2031 |
| `CapabilitiesDisabled` | REQ-2035 |

Each variant carries the names needed to locate the defect.

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `role.rs`: policy parsing, cast extension parsing
- `capability.rs`: meta-act parsing, authority past, `seat_state`,
  `epoch_fold`, `anchor_walk`, `round_membership`, `send_steps`, designation, finality computation
- `projection.rs`: `project` unchanged; `verify_with_capabilities` composes it

### Effectful Shell (orchestrates I/O, calls pure core)
- Consumers (cbcl-bus, hark): store the log, run the arbiter, deliver to
  recipients, facet holders and new seat holders (REQ-2042), count
  rejections, persist equivocation evidence.

### Boundary Contracts
`Message`, `ContentHash`, `MessageStore` (read-only), `CapVerdict`,
`EquivocationEvidence`.

### Dependency Rule
The pure core never calls the arbiter. The arbiter is a thread participant
whose epochs arrive as messages.

### Enforcement
`capability.rs` imports nothing outside `cbcl-core`; review checks this.

## Test Specifications

Each example-based test below pairs with the REQ of the same number. A `b` suffix, or a number from 2046, marks a test for a REQ numbered in the 2040s. Each covers the positive case, the negative-input case and,
where the REQ prohibits an action, the prohibited case. Fixtures extend the
SPEC-014 `checklist` and auction corpora with an incident dialect. Its roles
are:
- `commander`, singleton: `:delegate (transfer (facet assign))
  :recover-by observer :appoint (responder)`, where `resolve` is a choice act;
- `responder`, indexed: `:delegate (share redelegate (facet finding))`;
- `observer`, indexed, fixed, with a Send step `note`.
Its protocol: `request :from commander`, then `report :from responder`
(predecessor `request`), then `close :from commander` over `(all report)`.
`finding`, `propose-fix` and `assign` are further responder and commander
sends. `resolve` is a commander choice.

**Core** (writable in one sitting with the existing test harness): every
example test below.
**Depth** (needs proptest generators, fuzz targets or Lean work; owner HOC):
TEST-2040 through TEST-2045, the property half of TEST-2054, and the Lean
obligations in Open.

**TEST-2000: Policy parses.** Positive: the incident dialect yields the
stated `RolePolicy` per role. Negative: a duplicate `:delegate` clause
yields `MalformedPolicy`.

**TEST-2001: Fixed default.** Every SPEC-014 fixture dialect yields
`RolePolicy::fixed()` for every role.

**TEST-2002: Policy is signed.** Stripping `:delegate` from a signed dialect
fails R4 verification.

**TEST-2003: Policy names declared things.** `:appoint (ghost)` yields
`PolicyNamesUnknownRole`. `(facet finding)` on `commander` yields
`FacetActNotInRole`. `(facet resolve)` on `commander` yields
`FacetOverChoice`.

**TEST-2004: Indexed targets only.** `commander :delegate (share)` yields
`ShareOnSingleton`. `:appoint (commander)` yields `ShareOnSingleton`.

**TEST-2005: Anchored rounds only.** The auction dialect with
`(* bidder :delegate (share))`, whose counted `reveal` follows one act,
installs. A variant whose counted performative follows an `(all …)` step
yields `DynamicRoleInFanIn`. With `(* bidder :delegate (transfer))`, both
install.

**TEST-2006: Cast extension.** A root with `:arbiter @hub :fixed
(responder)` parses. Then a share grant in `responder` is rejected with
`ModeNotPermitted`. `:fixed (ghost)` yields `MalformedCast`.

**TEST-2007: Issuer holds the seat.** Positive: root responder @eli grants a
share to @diag. Negative: @cy, holding no responder seat, grants and gets
`IssuerLacksSeat`.

**TEST-2008: Mode and acts permitted.** A `transfer` grant in `responder`
yields `ModeNotPermitted`. A commander facet grant without `:acts` yields
`MalformedMetaAct`. One with `:acts (resolve)` yields `FacetActNotPermitted`.

**TEST-2009: Never widen.** A facet `(finding)` parent with a child granting
`(finding propose-fix)` yields `WideningGrant`. A `facet` parent with a
`share` child yields `WideningGrant`. A child of a parent bounded at epoch 4
carrying `:until (epoch 6)` yields `WideningGrant`; one with no `:until` has
bound 4.

**TEST-2010: Redelegate bit.** A child of a grant issued with
`:redelegate #f` yields `RedelegateNotPermitted`.

**TEST-2011: Chain bound.** A chain of 8 grants resolves. A chain of 9
yields `ChainTooLong`.

**TEST-2012: No expiry without arbiter.** A grant with `:until (epoch 4)`
in an arbiter-less thread yields `UntilWithoutArbiter`.

**TEST-2013: Designation and confused deputy.** @diag holds facet G1
`(finding)` from @eli and share G2 from @cy. An act `propose-fix :under G1`
is a `Violation` with `ActNotCovered`, even though G2 covers it. The same
act under G2 is `Valid`. A `resolve` act `:under G2` yields
`SeatRoleMismatch`.

**TEST-2014: Designation resolves.** An act naming a dialect act yields
`NotASeat`.

**TEST-2015: Root designation.** For @dana, holding one commander position,
`:under (root commander)`, `:under (root commander @dana)` and an omitted
`:under` give equal verdicts. A key holding two responder positions that
omits `:under` yields `AmbiguousRoot`.

**TEST-2016: Holder ratified by signature.** An act signed by @x with
`:sender @diag` under @diag's grant yields `HolderMismatch`.

**TEST-2017: Seat state is order-independent.** Every permutation of a set
with three grants, one accept and one revoke yields equal seat states. After
an accepted transfer, the `Moved` seat is live and not removed by its own
accept.

**TEST-2018: Projection unchanged.** `project` output for every role equals
the SPEC-014 output. A facet `(finding)` holder's Send set is `{finding}`.

**TEST-2019: Root position holders.** A `revoke` whose `:grant` names the
root wrapper hash yields `MalformedMetaAct` or `NotASeat`. After @dana's accepted transfer to @fay, an act by @fay under the `Moved` seat is `Valid`. An act by @dana under `(root commander)` yields `SeatNotLive`.

**TEST-2020: Transfer on accept.** @dana offers commander to @fay. Before
the accept: @dana `resolve` is `Valid` and @fay `resolve` under the transfer
grant yields `TransferNotAccepted`. After the accept, the reverse holds, and
@dana's facet to @tidy yields `SeatNotLive`.

**TEST-2021: Recipients and delivery.** After a share to @diag, a
responder-addressed act that omits @diag yields `RecipientMismatch`. After
a facet to @tidy, the delivery set of a commander-addressed act includes
@tidy and its recipient set does not. With the commander position contested,
a commander-addressed act needs no commander recipient.

**TEST-2022: Admission verdict composes.** A role-conformant act under a
live seat is `Valid`. The same act with a protocol-order error is the R5
`Violation`.

**TEST-2023: Removal in authority past.** After R1 revokes G1, an act under
G1 with R1 in `:seen` yields `SeatNotLive`. So is an act under G2 whose chain
contains G1. An act under G1 without R1 in its authority past is `Valid`.

**TEST-2024: Admission monotone.** Adding unrelated messages to the store
never changes a `Valid` admission verdict.

**TEST-2025: Finality and backdating.** In an arbiter thread, @diag sends
F2 under G1 whose authority past lacks R1. Admission is `Valid`. Epoch 3
lists R1 and covers F2: finality of F2 is `Void(SeatRemoved)`. An act in R1's
authority past, covered by epoch 3, is `Final`. An act under a seat bounded
at epoch 2 and covered by epoch 3 is `Void(BoundPassed)`. A grant G4 under G1,
concurrent with R1 and covered by epoch 3, is `Void(GrantRejected)` if R1 was
applied in an earlier epoch.

**TEST-2026: Epoch validity.** Each of these yields `EpochInvalid`:
- an epoch signed by a non-arbiter key;
- an epoch numbered 3 whose `:prev` is epoch 1;
- an epoch numbered 1 with a `:prev` other than `none`;
- an epoch whose `:order` lists an ordinary act;
- an epoch whose `:order` omits a removal in its batch.

**TEST-2027: Epoch fold.** Epoch 2 lists accepts A1 and A2 of two transfers
of the commander seat, in that order. A1 applies; A2 is void; acts under
A2's `Moved` seat covered by epoch 2 are `Void(SeatNotIssued)`. A seat
holder signs two concurrent resigns of its own seat: the first listed
applies, the second is void, and later epochs still finalise.

**TEST-2028: Equivocation.** Two admitted epochs numbered 4 yield `Frozen`
for messages not covered by epoch 3, and return `EquivocationEvidence` with
both hashes.

**TEST-2029: No arbiter, no finality.** Every verdict in an arbiter-less
thread has finality `NotApplicable`.

**TEST-2030: Late equivocation.** A message is `Final` under epoch 4a. Epoch
4b then arrives: the verdict becomes `Frozen`. A message covered by epoch 3
stays `Final`.

**TEST-2031: Reseat.** In an arbiter thread, observer @oli reseats the
commander position of @dana to @dana2. Before an epoch lists it, the reseat
has no effect. After epoch 5 applies it, three things hold:
- acts by @dana covered by epoch 5 and absent from the reseat's past are `Void`;
- a facet issued under @dana's seat is removed;
- an act by @dana2 under the `Reseated` seat, covered by epoch 6, is `Final`. Without an arbiter, or by a non-observer, the result is
`ReseatNotPermitted`.

**TEST-2032: Meta acts reach everyone affected.** A grant whose recipients
omit a root occupant, the arbiter, or the grantee yields
`MetaActRecipientMismatch`. A revoke whose recipients omit the revoked
holder yields the same.

**TEST-2033: Revocation follows the chain.** @eli revokes G3, issued by
@diag under G1, which @eli issued. Admitted. @cy revokes G1 and gets
`LacksAuthorityToRemove`. Revoking G1 removes G3.

**TEST-2034: Conservative extension.** For every non-meta message without
`:under` or `:seen` in the SPEC-014 fixture corpus, the admission verdict
equals `verify_causal_for_role`.

**TEST-2035: Opt-in installation.** With the default `Reject`, the incident
dialect fails installation with `CapabilitiesDisabled`. With `Accept`, it
installs. A policy-free dialect installs under both.

**TEST-2036: Authority links outside R5.** A protocol-valid `finding` with
`:under G1 :seen (R0)` has the same R5 verdict as without those links. The
same act citing G1 in `:caused-by` is the R5 `InvalidPredecessor`.

**TEST-2037: Conflicting terminations.** Without an arbiter, @dana's two
transfers to @fay and @gus are both accepted. A message whose authority past
holds both accepts finds no live commander seat: acts under either `Moved`
seat yield `SeatNotLive`. The same holds for a resign concurrent with an
accept, and for a revoke of a transfer grant concurrent with its accept.

**TEST-2038: Recovery role.** `commander :recover-by observer` with
`observer :recover-by commander` yields `RecoveryRoleInvalid`. A role
recovering itself, and a receive-only recovery role, yield the same.

**TEST-2039: Appointment.** @dana appoints @new to responder with
`:mode appoint`: admitted, and @new can send `finding`. Revoking that
appointment removes @new. The same grant under an observer seat yields
`ModeNotPermitted`.

**TEST-2042b: Authority past delivery.** A consumer harness seats @new by
appointment. @new's verifier, given only what the harness delivered, admits
@new's first act rather than returning `Unknown`.

**TEST-2043b: Reserved names.** A dialect declaring a performative `grant`
yields `ReservedName`.

**TEST-2044b: Thread scope.** An act whose `:seen` names a revoke of another
thread yields `CrossThreadLink`. An act whose `:seen` target is absent is
`Unknown`.

**TEST-2048: Accept admission.** @x, holding no seat, issues a transfer of
the commander seat to @x2, which @x2 accepts. The accept yields
`LacksAuthorityToRemove` and commander stays with @dana. An accept signed by a
key other than the grant's `:to` yields the same.

**TEST-2049: Two-hop contest.** Concurrent accepts move commander to @fay and
@hal. @fay moves on to @fay2 and @hal to @hal2. A message whose authority past
holds all four finds no live commander seat.

**TEST-2050: Share chain.** Revoking or reseating a share's parent removes the
share. Its issuer's upstream can revoke it.

**TEST-2046: Resign requires the seat.** @cy resigns @eli's seat and gets
`LacksAuthorityToRemove`.

**TEST-2047: Fan-in counts positions.** In a dialect with indexed `bidder`
counted by `(all bidder)`, a facet act satisfies its delegator's position.
A transferred seat's act satisfies the original position. Two acts from one
position count once. A `close` that references an act from a position shared
in after the anchor is `PositionOutsideRound`.

**TEST-2051: Round anchor.** @eli shares responder to @diag before @dana's
`request`, and the share is in `A(request)`. A `close :anchor request`
without @diag's `report` is `Violation`; with it, `Valid`. In a second
thread the share follows the request: `close` is `Valid` without @diag, and
a `close` that references @diag's `report` is `PositionOutsideRound`. A
`close` whose referenced reports walk to two different requests yields
`MixedRounds`. A `close` with no `:anchor` over a fixed role counts the
root positions. In the auction, each `reveal` walks through its own
`commit` to `open`, and `declare-winner :anchor open` is `Valid`.

**TEST-2052: Discharge.** Root responder @eli resigns after the request. A
`close` referencing the other reports and citing the resign in `:seen` is
`Valid`. Without the resign it is `Violation`. When @eli's `report` is also
in the close's authority past, the resign stands in for nothing. @cy's
revoke of a shared seat yields `LacksAuthorityToRemove` and discharges
nothing. Revoking the share's parent discharges the share. After an
accepted transfer of @eli's seat to @fay, @fay's `report` satisfies the
position. An @eli act whose authority past holds the accept is `Violation`. Three resigns and a `close` that references no report, citing
all three, is `Valid`. In an arbiter thread, a `close` whose cited resign is
`Void` in its covering epoch is `Void(EntryVoid)`.

**TEST-2053: Unlive grant.** Responder's Send steps are `{report}` and
`{finding, propose-fix}`. A `share` with `:acts (finding)` yields
`UnliveGrant`; with `:acts (finding report)` it is admitted. A `transfer` of
commander with `:acts (assign)` yields `UnliveGrant`. A `facet` with
`:acts (finding)` is admitted. A share whose new position fails
[[SPEC-014-role-layer-endpoint-projection#REQ-608]] on the [[SPEC-014-role-layer-endpoint-projection#TEST-641]] shape yields `NotCausallyLocal`.

**TEST-2054: Deadlock-freedom.** Core, scripted: @dana's `request` is the
anchor; then @eli shares to @diag, @fay resigns, and @eli's share is
revoked, delivered in every order. A `close :anchor request` is `Valid`
only when its authority past holds @fay's resign and the acts of the
remaining members; @diag's position is outside the round. Depth, property:
random grants, removals and acts under a scheduler that delivers every
message. No thread ends with an `Unknown` whose authority past and anchor
past are present.

**TEST-2055: Liveness claims.** A `finding :under G1` with G1 arriving
last is `Unknown` until then and `Valid` after. A `close` whose anchor's
authority past is incomplete is `Unknown` until it completes. In an arbiter
thread where every message is in an admitted epoch's batch, no finality
stays `Pending`, including messages whose admission is `Violation`.

**TEST-2040: Narrowing property (depth).** Take random chains within one role. The reduced seat's act set is the intersection of every link. Its mode and its bound are the minimum over the chain.

**TEST-2041: Determinism and order-independence property (depth).** For
random logs that include concurrent accept/accept, accept/reseat,
resign/accept and revoke/accept pairs, every admission verdict is equal
across delivery permutations.

**TEST-2042: Finality stability property (depth).** For random logs with an
honest arbiter, a finality verdict other than `Pending` never changes as
messages are added.

**TEST-2043: Designation cost guard (depth).** Operation counts for chain
lengths 1 through 8 stay within the NFR-2000 bound.

**TEST-2044: Typed reasons (depth).** Each rejecting fixture yields exactly
one `CapViolation` variant, matching the table in CON-2003. Each finality
`Void` fixture carries exactly one `VoidReason`.

**TEST-2045: Grammar fuzz (depth).** A fuzz target over CON-2000 and
CON-2001 with a round-trip oracle: `parse(serialise(x)) == x`.

## Traceability

| REQ | CON | TEST | Failure mode | Evidence |
|-----|-----|------|--------------|----------|
| REQ-2000–2003, 2043 | CON-2000, CON-2003 | TEST-2000–2003, 2043b, 2045 | FM-1 | ADR-2000, ADR-2007 |
| REQ-2004, 2039 | CON-2000, CON-2002 | TEST-2004, 2039 | FM-1 | ADR-2002, ADR-2007 |
| REQ-2005, 2041, 2046 | CON-2000, CON-2001, CON-2002, CON-2003 | TEST-2005, 2047, 2051 | FM-1 | ADR-2006 |
| REQ-2047 | CON-2002 | TEST-2052, 2054 | FM-6 | ADR-2014 |
| REQ-2048 | CON-2002, CON-2003 | TEST-2053 | FM-6 | ADR-2015 |
| NFR-2003 | CON-2002 | TEST-2054, 2055 | FM-6 | ADR-2015 |
| REQ-2038, 2031 | CON-2000, CON-2002 | TEST-2038, 2031 | FM-4 | ADR-2009 |
| REQ-2006 | CON-2001 | TEST-2006 | FM-1, FM-3 | ADR-2005 |
| REQ-2036, 2044, 2042 | CON-2001, CON-2002 | TEST-2036, 2044b, 2042b | FM-1, FM-2, FM-3 | ADR-2012 |
| REQ-2007–2011 | CON-2002 | TEST-2007–2011, 2040 | FM-2 | ADR-2001, ADR-2002 |
| REQ-2012 | CON-2002 | TEST-2012 | FM-3 | ADR-2011 |
| REQ-2013–2016 | CON-2001, CON-2002 | TEST-2013–2016 | FM-2 | ADR-2003 |
| REQ-2017–2021, 2032, 2040 | CON-2002 | TEST-2017–2021, 2032, 2033, 2046, 2041 | FM-1, FM-4 | ADR-2000, ADR-2007, ADR-2008 |
| REQ-2037, 2045 | CON-2002 | TEST-2037, 2048, 2049, 2050 | FM-4, FM-5 | ADR-2013 |
| REQ-2022–2024 | CON-2002 | TEST-2022–2024, 2041 | FM-3 | ADR-2004 |
| REQ-2025–2030 | CON-2002 | TEST-2025–2030, 2042 | FM-3, FM-5 | ADR-2004, ADR-2005 |
| REQ-2034 | CON-2002 | TEST-2034 | — | SPEC-014 Lean correspondence |
| REQ-2035 | CON-2002 | TEST-2035 | — | enable path |

Reading paths. Reviewer: the ADRs, then Open, then REQ-2017, REQ-2027 and
REQ-2025. Implementer: CON-2000 → CON-2001 → CON-2002 → REQ-2017 →
REQ-2027 → the core tests in number order. Stakeholder: the failure modes in
Context, then the Traceability table's failure-mode column.

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
| Revocation | ordered by an arbiter (ADR-2004) | f-conv-19, 23, 27; f-ocap-18, 19; f-certs-28, 29 |
| Concurrency | finality epochs, explicit order, no tie-break (ADR-2005) | f-conv-12, 14, 17, 18, 20, 21, 26 |
| Projection with change | membership from the authority past (REQ-2017) | f-session-02, 05, 07, 18–21 |
| Designation | explicit `:under` (ADR-2003) | f-ocap-01–06; f-certs-08, 14, 21, 23; f-conv-24 |
| Recovery | declared higher role (ADR-2009) | f-certs-30, 32, 33 |
| Read vs send | separate (ADR-2010) | f-conv-03, 04, 05, 29 |
| Round membership | positions live at the round anchor (ADR-2006) | f-session-02, 28, 29 |
| Removal mid-round | the removal discharges (ADR-2014) | f-session-27 |
| Liveness | claims under named fairness (ADR-2015) | f-session-23, 24, 26 |
| Position liveness | subtype check at grant (REQ-2048) | f-session-25 |

Sources (48), grouped as the survey cited them:

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
- Session types:
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

Full citations with URLs are in the theory's `source-doc` facts.

## Changelog

<details>
<summary>Revision history — 0.1.0 → 0.5.0</summary>

- 0.5.0 (2026-10-18) — normative. Two further session-type sources read in
  full (Deniélou and Yoshida §5; Keskin, Yoshida and van Glabbeek, ITP
  2026). Changes:
  - round anchors named by `:anchor`, anchor walks and round membership
    (REQ-2046); dynamic roles feed fan-in through anchored rounds (REQ-2005,
    REQ-2041, ADR-2006 rewritten). TEST-2005's share-auction case now
    installs. REQ-2041 counts round membership instead of root positions
  - an emptied position counts as met (REQ-2047, ADR-2014); finality
    re-checks counted acts and discharges (REQ-2025)
  - principal seats keep one act per Send step; REQ-608 at grant (REQ-2048)
  - named fairness and liveness claims (NFR-2003, ADR-2015); FM-6
  - `seat` recorded as a coined term; rotate mode, balancedness and Lean
    liveness added to Open
  - fourth adversarial review (2 blockers, 15 major, 10 minor) applied in
    this version; v0.4.0's round-3 fixes remain unreviewed

- 0.4.0 (2026-10-17) — normative. Third adversarial review (4 blockers, 9
  major, 9 minor) and third comprehension gate (passed). Changes:
  - accept admission (REQ-2045); inductive issuance along replacement
    chains; share chains; root designations resolved in the authority past
  - one-pass epoch fold in authority order; entries checked against their
    own admission; expiry in the fold; reseat as an admission termination
  - canonical authority-link list; seat attributes for root, moved and
    reseated seats; reserved `under` and `seen` parameters
  - remaining minor findings recorded in Open

- 0.3.0 (2026-10-17) — normative. Second adversarial review (16 new
  findings, 4 blockers) and second comprehension gate addressed. Changes:
  - the seat-state function (REQ-2017) with seat ids for moved and reseated
    seats and order-free terminations
  - the epoch fold (REQ-2027) and a positive finality rule (REQ-2025) that
    never consults admission
  - epochs list every removal (REQ-2026)
  - in-thread authority links (REQ-2044) and authority-past delivery
    (REQ-2042)
  - appointment as its own mode (REQ-2039)
  - no facets over singleton choices (REQ-2003)
  - sending, acyclic recovery roles (REQ-2038)
  - reserved names (REQ-2043)
  - explicit root designation when ambiguous (REQ-2015)
  - Orientation glossary and stolen-key behaviour
- 0.2.0 (2026-10-17) — normative. First adversarial review (19 findings, 5
  blockers) and the first comprehension gate addressed. Authority links,
  cascading removal, contested positions, explicit epoch order, expiry,
  facet act lists, fan-in by positions.
- 0.1.0 (2026-10-17) — first draft, from the `cap-epp-lit` literature
  survey. Normative.
</details>
