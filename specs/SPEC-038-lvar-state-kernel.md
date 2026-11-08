---
id: SPEC-038
title: LVar state kernel
status: draft
version: 0.3.0
last-updated: 2026-11-08
---

# LVar state kernel

## Orientation

Intent: an LVar state kernel. Each state field is a lattice variable in the
sense of [[LVars]], written only by joining the contributions of
authenticated, admitted acts. Authors may inspect revisable snapshots; only
stable threshold facts and attributable frozen values reach the execution
layer. Replicas with equal accepted sets observe equal values. Successful
threshold answers agree unless the combined history faults; frozen underlying
values agree for the same earliest freezer. Ordinary snapshots at different
replicas may differ. This restates the R7 kernel of
[[SPEC-019-state-rules]]; every state field becomes a term in one closed
lattice algebra.
The named failure is **a displayed value that an application acts on as if it
were final when the accepted set can still revise it**. Today the fold is a
set function but says nothing about which of its outputs may be acted on; the
host decides, and the guarantee stops at the fold.

For a dialect author: a **threshold** establishes a stable fact, a **snapshot**
describes a value that may change, and a **fault** identifies an inconsistent
history. "Three approvals have arrived" can be a threshold. "The current net
balance is ten" is a snapshot when debits or negative amounts are possible.
A threshold never silently changes its successful answer or returns to pending;
later conflicting evidence can instead fault the computation. A conflicting
opener faults dependent tallies rather than making their votes disappear.
These rules are specified by [[SPEC-038-lvar-state-kernel#ADR-3805]].

Controls: installation rejects revisable sum thresholds and `fault` as a
threshold alternative; nonnegative contributions are checked before admission;
initializer conflicts propagate to dependent fields; raw carrier evidence is
retained under merge. A host still supplies its own external-effect finality,
deduplication and recovery contract: a threshold is not an exactly-once effect.

The read-only context map exposes installed dialect identity, sealed thread
role rosters and current observation metadata as ordinary kernel data. Sealed
rosters can supply domains and membership reads. Replica-local observations
such as the frontier remain snapshots. The context primitive supplies data,
not a quorum policy or dedicated quorum arithmetic.
[[SPEC-038-lvar-state-kernel#CON-3804]] specifies the typed paths.

Metaphor: a notice board. Anyone with standing may pin a notice; nothing is
ever unpinned; a reader may ask "has at least this been pinned?" and get a
yes that never becomes a no; and the chair may seal the board, after which the
board at that seal can be read exactly. A later notice is excluded from that
sealed value and recorded as superseded, or faults the read when the author
selects the fault policy.

Structure:

```
   accepted set A  ──put: join g(a)──▶  ┌──────────── field lattice L_F ────────────┐
   ([[SPEC-019-state-rules]] R.1)       │  σ_F ∈ L_F, ⊥ ≤ σ_F ≤ ⊤        (CON-3800)  │
                                        │  σ_F = ⋁_{a ∈ A} g_F(a)   (morphism)       │
                                        └───────┬──────────────────┬────────────────┘
                                                │                  │
                     threshold read (CON-3801)  ▼                  ▼  freeze by verb (CON-3802)
                   ┌──────────────────────────────┐   ┌──────────────────────────────┐
                   │ t ∈ T, T pairwise incompatible│   │ exact read after the freeze; │
                   │ yields the unique t ≤ σ_F     │   │ later contribution: supersede │
                     │ stable, or explicit fault     │   │ or Violation (ADR-3802)      │
                   └──────────────────────────────┘   └──────────────────────────────┘
                     only these two reads reach the execution layer; a bare
                     projection of σ_F is a snapshot (REQ-3805)
   arrows point inward: the pure kernel never reads the host; the host reads it
```

Decisions: [[SPEC-038-lvar-state-kernel#ADR-3800]] LVars as the kernel model ·
[[SPEC-038-lvar-state-kernel#ADR-3801]] user definition in three tiers: compose freely, declare finite lattices and tables verified at install, never supply code ·
[[SPEC-038-lvar-state-kernel#ADR-3802]] freeze against a concurrent write: supersede by
default, fault by declaration · [[SPEC-038-lvar-state-kernel#ADR-3803]] a conflict top in
every lattice · [[SPEC-038-lvar-state-kernel#ADR-3804]] the sixteen heads stay as
abbreviations, no wire change.

Load-bearing: [[SPEC-038-lvar-state-kernel#REQ-3800]] every field is a term ·
[[SPEC-038-lvar-state-kernel#REQ-3809]] derived fields over the product, contributions never read revisable fields ·
[[SPEC-038-lvar-state-kernel#REQ-3802]] threshold reads ·
[[SPEC-038-lvar-state-kernel#REQ-3803]] freeze · [[SPEC-038-lvar-state-kernel#REQ-3806]]
quasi-determinism · [[SPEC-038-lvar-state-kernel#NFR-3800]] explicit evaluation cost bounds.

Open: the remaining whole-kernel proof bridges are owned by the SPEC-038
implementer: compose the faulting native cached reader with the concrete
authored compiler, close cached-upper-set validator correspondence, and retain
the explicit installation/wire/rank/renderer boundaries. Whole concrete source
binding, regenerated-selector fault growth, and clear-history cached cuts are
proved; they do not alone establish complete native reader correspondence.
Progress and the escrow function `bounded-counter` retain their
author-facing forms over the shared history-backed kernel path
([[SPEC-038-lvar-state-kernel#ADR-3806]]). Sequence lattices are out of scope.

Detail: the Vocabulary section below for the names (lift, display, LVar, put,
threshold read, frozen read, snapshot, stable, kernel); [[SPEC-019-state-rules]]
for the fold this restates;
[[SPEC-036-state-kernel-correctness]] and [[SPEC-037-state-kernel-sec]] for the
theorems this subsumes; [[IMPL-030-lvar-state-kernel]] for the plan;
[[protocol-model]] for the refinement chain this kernel sits at the end of.

## Amendment Channels

The CBCL maintainer may amend this specification through an explicit decision
in the implementation conversation, recorded in its changelog and decision
artifacts. No amendment may silently reinterpret a signed balance as gross
credits, discard conflict evidence, or claim external-effect finality from a
threshold alone.

This specification authorises a new pure module in `cbcl-core` that denotes
existing rules as lattice terms and is checked against the shipped fold, two
new optional state-clause forms (`threshold`, `freeze`), a conflict marker in
rendered fields, and new Lean theorems. It does not authorise changes to
addresses, to the admission monitor, to the verdict algebra of
[[SPEC-003-verification-lattice]], or to the wire form of any existing clause.
Any such change is a separate specification.

It also authorises the additive `nonnegative` integer shape type required to
recognize monotone amount contributions. Existing `number` shapes retain their
signed meaning and existing wire forms retain their addresses.

## Background

[[SPEC-019-state-rules]] R.2 fixes sixteen rule heads and proves, per head, that
the fold is a set function of the accepted acts ([[SPEC-036-state-kernel-correctness]]).
[[SPEC-037-state-kernel-sec]] proves conditional strong eventual consistency.
Neither says which outputs of the fold are safe to act on. The docs note that
"the displayed value itself need not increase monotonically", and the execution
layer ([[state-refinement]], [[SPEC-037-state-kernel-sec]]) says effects need
finality conditions without naming them.

LVars ([[LVars]]: Kuper and Newton 2013; Kuper, Turon, Krishnaswami and Newton
2014) are lattice-valued variables with three operations: `put` joins a value
in; a *threshold read* names a set of pairwise-incompatible lattice elements and
returns whichever one the variable has reached, which is deterministic in any
write order because at most one can ever be reached; and *freeze* makes the
variable exact, after which a read returns the full value and a further `put`
that would move it is an error. The LVish theorem is quasi-determinism: every
execution gives the same result or raises that error.

The factorisation recorded in the refinement-chain work shows that thirteen of
the sixteen heads are already lifts of a per-act contribution into a product of
grow-only sets, maps or a chain, followed by a projection; two (`progress`,
`bounded-counter`) have no summarising carrier, since an act's position or an
operation's validity depends on its cited ancestors, so their only carrier is
the set of acts itself and their post-map is a least fixed point over
citations; and `initial` is a
morphism into a lattice with a conflict top whose displayed value is retracted
on conflict. This specification makes that structure explicit and adds the two
reads LVars require.

## Vocabulary

These names are used throughout this specification and SHALL be used in code,
documentation and theorems that implement it. Where an older name is retained
for compatibility it is noted.

- **Accepted set** `A`: the finite set of acts admitted into a thread's history
  ([[SPEC-019-state-rules]] R.1). Unique by address; closed under cited
  predecessors; the only input to the kernel.
- **Carrier** `L`: a bounded join-semilattice with bottom `⊥` and top `⊤`,
  chosen from [[SPEC-038-lvar-state-kernel#CON-3800]] or declared under
  [[SPEC-038-lvar-state-kernel#CON-3803]]. `⊤` means conflict and carries
  evidence ([[SPEC-038-lvar-state-kernel#REQ-3804]]).
- **Contribution** `g : Act → L`: what one act adds to a carrier. A function of
  that act alone, never of other acts or other fields. A domain-governed
  contribution retains raw evidence for the display to interpret
  ([[SPEC-038-lvar-state-kernel#REQ-3809]]).
- **Lift**: the map `A ↦ ⋁_{a ∈ A} g(a)` from accepted sets into `L`. It is the
  unique join-homomorphism out of the free join-semilattice on acts that
  extends `g`; its laws, order independence, duplicate insensitivity and
  `lift(A₁ ∪ A₂) = lift(A₁) ⊔ lift(A₂)` on causally closed sets, are the
  associativity, commutativity and idempotence of `⊔`. *The R7 fold of
  [[SPEC-019-state-rules]] is the lift followed by a display*; the name `fold`
  is retained for the `cbcl_core::state::fold` API and means lift-then-display.
- **Display** (post-map): a function from a carrier element, and the earlier
  fields of the clause, to a rendered value. It may forget lattice structure. It
  is classified as a *morphism* (distributes over `⊔`), *monotone* (preserves
  the carrier order into the codomain's order) or *revisable* (neither).
- **Term**: a selector, a contribution and a carrier, composed by products,
  keyed maps and displays ([[SPEC-038-lvar-state-kernel#CON-3800]]). A
  *summarising carrier* is one smaller than the set of acts; the two *closure
  heads*, `progress` and `bounded-counter`, have none and their display is a
  least fixed point over citations ([[SPEC-038-lvar-state-kernel#REQ-3808]]).
- **LVar**: a state field, viewed as a lattice variable: its carrier, its
  current element `σ_F = lift(A)`, and its reads. **LVar store**: a clause's
  fields together, whose state is the product lattice `∏_F L_F`
  ([[SPEC-038-lvar-state-kernel#REQ-3809]]).
- **Put**: the change to an LVar when an act is admitted, `σ_F := σ_F ⊔ g_F(a)`
  ([[SPEC-038-lvar-state-kernel#REQ-3801]]). Puts are the only writes.
- **Threshold read**: an observation over a declared pairwise-incompatible set
  `T ⊆ L_F`, yielding the unique `t ∈ T` with `t ≤ σ_F` or `pending`
  ([[SPEC-038-lvar-state-kernel#REQ-3802]]). Successful results are stable;
  conflict is a separate terminal failure. Typed against the carrier with a
  verified monotone read, never an arbitrary revisable display.
- **Freeze**: a role-permitted act after which an LVar is exact. **Frozen
  read**: a read of `σ_F` after its freeze, carrying the freezing address
  ([[SPEC-038-lvar-state-kernel#REQ-3803]]).
- **Snapshot**: any displayed value that is neither a reached threshold nor
  frozen. Readable, revisable, no finality from this kernel
  ([[SPEC-038-lvar-state-kernel#REQ-3805]]).
- **Stable**: a display that is monotone into booleans or integers, hence
  admissible as a threshold element source ([[SPEC-038-lvar-state-kernel#REQ-3810]]).
- **Quasi-determinism**: the kernel's theorem: replicas with equal accepted
  sets observe equal thresholds and frozen values, and any two replicas observe
  either the same value or `⊤` with evidence naming the acts in conflict
  ([[SPEC-038-lvar-state-kernel#REQ-3806]]).
- **Kernel**: two readings, both intended. The engineering reading: the pure,
  closed, proven core, `cbcl_core::state` and `cbcl_core::lattice`, that hosts,
  transport and cryptography sit outside of. The algebraic reading: the kernel
  of the lift, the congruence on accepted sets `A₁ ~ A₂ ⇔ lift(A₁) = lift(A₂)`;
  strong convergence ([[SPEC-037-state-kernel-sec#REQ-3700]]) says set
  equality refines it, and the state lattice is the quotient of act-sets by it.
  "State kernel" therefore names the relation that says which histories are
  indistinguishable by state, as well as the code that computes it.

## REQ-3800: Every field denotes a lattice term

Every state field SHALL denote a term of the closed lattice algebra of
[[SPEC-038-lvar-state-kernel#CON-3800]]: a selector on accepted acts, a per-act
contribution `g` into a lattice carrier, the join over the selected acts, and a
post-map to the displayed value. The join half of every term SHALL be a
join-homomorphism from `(℘(A), ⊆)` on causally closed accepted sets: for any
two accepted sets `A₁`, `A₂` each closed under cited predecessors,
`σ(A₁ ∪ A₂) = σ(A₁) ⊔ σ(A₂)`, including sets with different openers.
A domain-governed term SHALL retain raw initializer evidence and raw
contributions in its carrier; domain filtering SHALL be a display operation,
not removal of carrier evidence. The carrier MAY retain the accepted acts by
address where a smaller summary cannot preserve that evidence. Conflicting
initializers SHALL fault dependent displays and thresholds with their evidence.
The sixteen shipped heads SHALL be abbreviations
of terms, and the term's displayed value SHALL equal the shipped fold's value
on every conflict-free conformance vector. Conflict rendering follows
[[SPEC-038-lvar-state-kernel#REQ-3804]] and
[[SPEC-038-lvar-state-kernel#REQ-3807]].
Trace: [[SPEC-038-lvar-state-kernel#TEST-3800]], [[SPEC-038-lvar-state-kernel#CON-3800]].

## REQ-3801: Put is a join of accepted contributions

Admitting an act SHALL change a field only by joining that act's contribution:
`σ := σ ⊔ g(a)`. Puts SHALL commute and be idempotent, so that set union of
accepted acts is the only merge, duplicate delivery changes nothing, and the
invariance of [[SPEC-019-state-rules#REQ-1915]] follows from the algebra rather
than per rule.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3800]].

## REQ-3802: Threshold observations

A dialect MAY declare a threshold observation
`(threshold name field t₁ … tₙ)` over a field whose lattice carrier admits the
named elements. Installation SHALL reject a threshold set whose elements are
not pairwise incompatible, where two elements are incompatible when no lattice
element lies above both other than ⊤. The fold SHALL render the observation
as `reached tᵢ` for the unique successful element reached, or `pending`.
Conflict SHALL be a separate terminal `fault` outcome with evidence, checked
before successful alternatives; `fault` SHALL NOT be a threshold element.
A reached observation SHALL never return to pending or change its successful
element as the accepted set grows. A later conflict MAY replace the current
successful observation with a fault, without erasing its historical occurrence.
Successful observations SHALL agree across replicas that contain their
supporting acts and whose dependent carriers are non-conflicting.

A sum threshold SHALL observe the actual sum of its declared source, not one
half of a signed counter. Installation SHALL reject a sum threshold unless
every possible source contribution is recognized as a nonnegative integer and
the source cannot remove or revise those contributions. Signed counters and
revisable register sums SHALL remain snapshots. A grow-only numeric `events`
field whose writer requires `nonnegative` is an admissible source.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3801]], [[SPEC-038-lvar-state-kernel#TEST-3803]],
[[SPEC-038-lvar-state-kernel#CON-3801]].

## REQ-3803: Freeze

A dialect MAY declare that a verb freezes a field, `(freeze field verb)`, with
the verb's `:from` role as the only permitted freezer. After an accepted act of
that verb, reads of the field SHALL be exact: the rendered value carries
`frozen` with the freezing act's address, and the host MAY act on it as final
with respect to this dialect. A contribution to the field accepted after, or
concurrent with, the freeze SHALL be handled by the field's declared policy
([[SPEC-038-lvar-state-kernel#ADR-3802]]): under `supersede` it is excluded from
the frozen value and recorded; under `fault` the field joins to ⊤ with both
addresses as evidence. In both cases the late act is attributable: it is a
signed, accepted act that cites or fails to cite the freeze.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3802]], [[SPEC-038-lvar-state-kernel#CON-3802]].

## REQ-3804: A conflict top in every lattice

Every field lattice SHALL have a top element ⊤ meaning conflict, carrying the
addresses in conflict as evidence. Contributions that cannot coexist SHALL join
to ⊤: a second distinct opener for an `initial` field, a resource fork for a
`bounded-counter`, and a late write under the `fault` freeze policy. ⊤ SHALL be
sticky under growth of the accepted set and SHALL be rendered as
`{"status":"fault","evidence":[…]}` uniformly across heads. The displayed value
of `initial` SHALL therefore be monotone in the lattice: it moves from absent to
a value to fault and never back.
An initializer fault SHALL propagate to every field whose domain depends on
it, to derived fields depending on those fields, and to their thresholds.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3804]].

## REQ-3805: Snapshot discipline for projections

A rendered field value that is neither a reached threshold, frozen, nor an
immutable installed/sealed context projection SHALL be marked as a snapshot in the state schema, and the host documentation SHALL
state that an external effect fired on a snapshot has no finality guarantee
from this kernel. The existing fold outputs remain available unchanged; this
requirement adds the marking, not a restriction.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3805]].

## REQ-3806: Quasi-determinism

The Lean model SHALL prove: for two replicas satisfying the delivery premises of
[[SPEC-037-state-kernel-sec#CON-3700]] and any field, successful threshold
results agree unless their combined history has a conflict, and successful
frozen underlying values agree for the same earliest freezer. A conflict
observation carries a finite witness of acts in conflict. Every replica that
eventually accepts that witness SHALL fault with evidence containing it;
additional accepted conflicts MAY enlarge the evidence. Equal accepted sets
SHALL produce exactly equal observations and canonical evidence.

Under the complete finite-history premise of [[SPEC-037-state-kernel-sec]],
replicas SHALL eventually agree on the complete observation. For ongoing
histories the guarantee is stable successful facts and per-witness
dissemination, not a final snapshot of an infinite history. Frozen values are
stable; excluded-contribution metadata MAY grow. Conditional strong eventual
consistency ([[SPEC-037-state-kernel-sec#REQ-3702]]) SHALL be recovered as the
case in which ⊤ never occurs. The proof SHALL introduce no sorry or custom axiom.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3806]].

## REQ-3807: No change to existing wire forms or addresses

Every existing dialect SHALL parse, install and fold identically. Every
conformance vector in `test-vectors/state/` SHALL produce byte-identical
addresses and verdicts, and identical rendered state except for the additive
`frozen`, `fault` and threshold members this specification introduces. A fault
SHALL also appear when existing initializer or resource semantics detect a
conflict, and SHALL propagate to dependent fields; no declaration is required
to make an inconsistent history visibly fail. Conflict-free existing vectors
SHALL remain unchanged.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3807]].

## REQ-3808: Closure heads

`progress` and `bounded-counter` SHALL be modelled as lifts with the identity
contribution into the set of selected acts under union, which is a
join-homomorphism like every other head, and a post-map that is a least fixed
point over cited acts. They SHALL be distinguished from the other heads only by
the absence of a summarising carrier: no per-act contribution smaller than the
act determines their value, so they cannot be evaluated incrementally per
contribution. Their existing proofs ([[SPEC-034-owned-progress-closure]],
[[SPEC-019-state-rules#CON-1908]]) are retained; the monotonicity of their
post-maps is as proved there: `progress` is monotone, a resource `fault` is
sticky, and `ready` and the rights are revisable. They SHALL participate in
freeze. `progress` supports successful threshold reads on reaching its bound;
resource conflicts propagate as separate terminal faults, never successful
threshold alternatives. Both heads use the same history-term and closure-post
interface, retaining their specialized algorithms under
[[SPEC-038-lvar-state-kernel#ADR-3806]].
Trace: [[SPEC-038-lvar-state-kernel#TEST-3800]].

## REQ-3809: Fields over the product lattice

The state of a clause SHALL be the product lattice `∏_F L_F` of its fields, and
a field MAY be *derived*: a post-map over earlier fields of the same clause, in
clause order, as `histogram` and `sum` already are. A derived field's post-map
SHALL come from the closed menu of [[SPEC-038-lvar-state-kernel#CON-3800]]
extended with conjunction and comparison of monotone reads, so that a threshold
over several fields, for example `(and (count approvals 2) (exists closed))`,
is a threshold on the product and inherits the stability of
[[SPEC-038-lvar-state-kernel#REQ-3802]]. A contribution `g` SHALL NOT read any
state field; initializer evidence SHALL instead be retained in the carrier
and domain predicates evaluated by its display. A put that depended on a
revisable field would make admission or the fold read its own output, which is
the feedback the stratification result of [[SPEC-019-state-rules#REQ-1914]]
forbids. Cross-field conditions on revisable values are therefore expressible
only as derived snapshots or as thresholds, never as selectors.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3800]], [[SPEC-038-lvar-state-kernel#TEST-3801]].

## REQ-3810: User-defined finite lattices verified at installation

A dialect MAY declare a finite lattice, a table-defined contribution and a
table-defined post-map ([[SPEC-038-lvar-state-kernel#CON-3803]]). Installation
SHALL reject the declaration unless: the join table is total on the declared
elements; join is commutative, associative and idempotent; the declared bottom
is the identity of join and the declared top absorbs it; every contribution
table maps into the declared elements; and every post-map table marked `stable`
is monotone from the lattice order into its codomain's order (booleans under
false ≤ true, integers under ≤). A field over such a lattice SHALL then satisfy
[[SPEC-038-lvar-state-kernel#REQ-3800]] and [[SPEC-038-lvar-state-kernel#REQ-3801]]
with no further proof, and a `stable` post-map SHALL be admissible as a
threshold element source under [[SPEC-038-lvar-state-kernel#REQ-3802]]. The
element count SHALL be bounded by the clause's `max-list`.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3808]], [[SPEC-038-lvar-state-kernel#CON-3803]].

## REQ-3811: Read-only dialect and thread context

A dialect author SHALL be able to read installed dialect metadata, validated
thread metadata and the current accepted-set observation through a typed,
read-only context map in the LVar kernel. Context supplies ordinary data to
kernel operations; it SHALL NOT introduce quorum policies or change admission
permissions. Sealed role rosters SHALL support existing domains and membership
thresholds without duplicating the cast in business payload fields.

The context SHALL expose dialect signing identity, self-addressed body name,
authored name, author, role declarations and state bounds; thread ID, root,
initiator, business opener and sealed role occupants; and observation accepted
count and causal frontier. Missing root evidence leaves thread metadata absent,
not an invented empty roster. Incompatible roots/bindings fault dependent reads.
Fixed installed/sealed projections SHALL be marked `context` in the schema;
whole context/thread objects and current observations remain snapshots. No local
wall clock or arbitrary host configuration supplies these values. Compilation
caches SHALL be rebuilt from the installed dialect and excluded from wire
identity.
Trace: [[SPEC-038-lvar-state-kernel#CON-3804]],
[[SPEC-038-lvar-state-kernel#TEST-3809]].

## NFR-3800: Cost

For `n` accepted acts and total state-expression size `t`, ordinary collection
selection and rendering SHALL stay within `O(t n log(n + 1))` work under the
existing bounded-key and expected hash-index lookup model. A frozen clause with
`d` distinct causal cuts and at most `f` earliest concurrent freezers per field
SHALL stay within `O(t (d + 1) n log(n + 1) + t n f)` work: scoped reads are
memoized, and complete concurrent-freeze witness evidence visits each frontier
cut. In particular, an unbounded number of concurrent earliest freezers can
make evidence collection quadratic in accepted history size. The implementation
SHALL NOT describe end-to-end evaluation as strictly linear. The delegated
protocol-position and resource validators retain their existing R2 bounds;
their validation cost SHALL be stated separately from collection evaluation.

The pairwise-incompatibility check of a threshold set of `k` elements SHALL
perform `O(k²)` constant-work pair comparisons at installation and none at fold
time. A finite carrier with `m` elements MAY preprocess its ordinary projected
upper sets in `O(m²)` comparisons before those pair checks. Verifying a
user-defined lattice of `m ≤ max-list` elements SHALL take `O(m³)` table lookups
at installation and none at fold time. These are operation-count bounds, not
wall-clock benchmark claims.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3803]], [[SPEC-038-lvar-state-kernel#TEST-3808]].

## CON-3800: The lattice algebra

Interface: a pure module `cbcl_core::lattice` with a denotation
`factor(&Rule) -> Option<Factored>` (all installed heads factor; unresolved
finite declarations have no denotation), an
evaluator `evaluate(&Factored, &Ctx, done) -> (L, Value)`, and `L::join`.

Grammar of terms (abstract; no new wire syntax in this contract):

```text
term         := lift(select+, contribute)            ; join over selected acts
              | pair(term, term) | earlier(field)
              | history(dependency-verbs)             ; identity contribution of accepted acts
contribute   := flag | address | field(key) | entry(key) | amount(key)
              | clocked(value-key, clock-key)        ; chain under (hlc, signer, address)
              | write(group) | replaced(group)        ; the W and R halves of supersession
              | sole(key)                             ; initial: ⊥ | one | ⊤
group        := none | signer | field(key)
select       := (verb, raw?)                          ; raw ignores domain filters
post         := identity | size | difference
              | current(post) | group-by(group, post) | pick-lww(value-key, clock-key)
              | distinct(key) | histogram(earlier) | sum(earlier)
              | closure(progress | bounded-counter)  ; existing native validators
carrier L    := bool | addrs | vals | entries | amounts | chain | writes | replaced | sole | pair(L, L)
              | history                             ; raw acts and initializer evidence under union
```

Pre-conditions: acts are unique by address; the clause installed under R7.
Post-conditions: for every factored head, (i) `L` is a join-homomorphism from
accepted sets, (ii) on conflict-free histories the displayed value equals
[[SPEC-019-state-rules]] R.2's fold. On conflicting histories display follows
[[SPEC-038-lvar-state-kernel#REQ-3804]]. Error model: none; the evaluator is total.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3800]], [[SPEC-038-lvar-state-kernel#REQ-3801]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3800]].

## CON-3801: Threshold clause

Wire grammar, an entry of the `state` clause recognised by the existing
S-expression recogniser and checked at install, no new lexical forms:

```text
entry     := … | "(" "threshold" name field element+ ")"
element   := scalar | "(" "count" integer ")" | "(" "member" scalar ")"
           | "(" "sum" integer ")" | "(" "progress" integer ")"
shape-type := … | "nonnegative"                       ; integer >= 0, existing numeric bounds apply
```

`element` forms are typed against the field's carrier, never against the
displayed value, so that a threshold over a superseding or observed-remove
carrier is stated on its grow-only halves (an address was written, an address
was replaced) rather than on membership, which is not monotone: `count n` against
`addrs`, `member x` against `vals` or `entries`, `sum n` against a grow-only
numeric events carrier whose writer requires `nonnegative`, `progress n`
against the progress chain, and a bare scalar against `bool` (`#t`). A
`history` carrier retains the raw contributions and initializer evidence; the
read first checks initializer conflicts, then reads the domain-admitted
contributions. Install rejects a signed counter or revisable map as a sum
threshold source, `fault` as an element, mistyped elements, and compatible
pairs. Rendering: `{"status":"reached","element":…}`,
`{"status":"pending"}`, or the uniform
`{"status":"fault","evidence":[…]}` as a field named `name` in clause order.
The `nonnegative` shape type recognizes only integers >= 0 before admission;
no clamping, omission or conversion of negative contributions is permitted.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3802]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3801]], [[SPEC-038-lvar-state-kernel#TEST-3803]].

## CON-3802: Freeze clause

```text
entry  := … | "(" "freeze" field verb [policy] ")"
policy := "supersede" | "fault"                      ; default supersede
```

Pre-conditions: `verb` is a performative with a `:from` role; `field` is a
declared state field. Receipt admits the freezing act like any other. The
frozen value is computed over the freezer's accepted causal past, including
the freezing act itself; other contributions are after or concurrent with it.
The default `supersede` policy renders
`{"frozen":"<address>","superseded":[…],"value":…}`, with excluded contributor
addresses sorted and unique. The `fault` policy renders the uniform fault
with the freezer and excluded contributors as evidence.

The earliest causal freeze determines the cut. Causally later freezes do not
change that cut; concurrent earliest freezes fault with their addresses as
evidence under either policy. A field may have only one freeze declaration.
An initializer/resource/dependency fault in the accepted history SHALL NOT be
hidden by freezing an earlier cut. Derived fields read the underlying frozen
value and propagate dependency faults.

A `supersede` freeze can revise an earlier snapshot. Installation therefore
rejects a threshold whose source has that policy; the diagnostic SHALL suggest
an unfrozen monotone arrival field or the `fault` policy. A threshold over a
field frozen with `fault` remains reached or explicitly faults, never pending.
Error model: install rejects an undeclared field or verb, a verb without a
`:from` role, duplicate freeze declarations, or a revisable threshold source.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3803]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3802]].

## CON-3803: User-defined finite lattices

Wire grammar, entries of the `state` clause recognised by the existing
S-expression recogniser:

```text
entry        := … | "(" "lattice" name "(" "elements" symbol+ ")"
                                     "(" "bottom" symbol ")" "(" "top" symbol ")"
                                     "(" "join" "(" symbol symbol symbol ")"* ")" ")"
rule         := … | "(" "lift" verb "(" "into" name ")" "(" "contribute" entry-row+ ")"
                                 [ "(" "project" ["stable"] "(" out-row+ ")" ")" ] ")"
entry-row    := "(" key scalar symbol ")"     ; field, field value → element
out-row      := "(" symbol scalar ")"         ; element → displayed scalar
```

Pre-conditions: `name` is unique among lattices and fields; every symbol in a
`join` row, `entry-row` or `out-row` is a declared element; `n ≤ max-list`.
Names and element symbols follow the state field-name grammar. Bottom and
conflict top are distinct. The declared top denotes conflict, not the greatest
ordinary business value; an author needing ordinary levels `lo`, `mid`, `hi`
adds a separate element for conflict top. Every matching contribution row is
joined, so row order does not select a winner. If a project table is present,
it SHALL have exactly one scalar output per declared element. A stable table
uses one ordered codomain throughout: booleans or integers.
Post-conditions: on installation the checks of
[[SPEC-038-lvar-state-kernel#REQ-3810]] have passed, the field is a lift whose
join is the declared table, and its display is the `project` table applied to
the joined element, or the element's symbol when no `project` is given. An act
whose fields match no `entry-row` contributes the bottom. Error model: install
rejects with the first failing law and the witnessing elements, for example
`join not commutative: (a b) ≠ (b a)`; no repair.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3810]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3808]].

## CON-3804: Context projection

Recognized grammar (paths are closed and validated against installed metadata):

```text
rule := … | (context [path])
path := dialect [address|body-address|name|author|roles [role]|bounds [bound]]
      | thread [id|root|initiator|opener|roles [role]]
      | observation [accepted-count|frontier]
bound := max-fields | max-list | max-number | max-string
root-pin := :dialect string
  ; decoded string is exactly "sha256:" followed by 64 lowercase hex digits
```

An empty path returns the complete map. Nested role names must be declared.
`address` is the dialect signing hash used by pins; `body-address` is its
self-addressed body name, independent of an authored alias. `name` is the
installed dialect name. The root's cast is recognized using the existing role
recognizer, including optional dialect pin validation. The strict-wire form is
`:dialect "sha256:<hex64>"` in the cast wrapper's existing pin position; malformed
prefixes, lengths and non-lowercase-hex digests fault without normalization.
Existing typed symbol pins remain supported for in-process compatibility; the
strict lexer symbol alphabet is unchanged. This additive wire form extends the
optional pin of [[SPEC-014-role-layer-endpoint-projection#REQ-628]] without
changing existing accepted forms or addresses. Unknown paths are
installation errors. Missing root evidence is absent; malformed casts and
incompatible roots/bindings render the standard attributable fault.

Context projections retain the accepted-history carrier under union and use the
shared kernel display path. Static metadata is compiled from the dialect;
thread metadata is reconstructed from accepted causal roots. A role-roster
projection can supply an existing data domain or membership threshold. Revisable
observation paths cannot supply contribution selectors or threshold carriers.
Freezing full/observation context accounts for every accepted act, including acts
excluded by application data domains. A historical cut cannot conceal a later
context-root conflict. Quorum policy and new arithmetic operators are outside
this context-access contract.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3811]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3809]].

## ADR-3800: LVars as the model of the state kernel

Decision: adopt the LVar store, with put, threshold read and freeze, as the
semantics the kernel aspires to, and quasi-determinism as its theorem.
Alternatives, with sources verified on 7 November 2026 ([[LVars]]): keep the fold
as an unclassified set function (status quo; leaves finality to hosts and gives
no exactly-once property); adopt CRDT state alone (gives the lattice but not the
read discipline); adopt Lasp's monotonic read, `read(x, v)`, which returns the
replica's state once it dominates a trigger (gives liveness but not a unique
answer: two replicas can return different states from one trigger, so it is a
snapshot in this specification's terms); adopt Hydro's lattice-typed dataflow
(gives morphism tracking, which [[SPEC-038-lvar-state-kernel#REQ-3809]] borrows,
but assumes cooperating replicas and has no freeze); adopt full Bloom^L with
user-defined lattices (gives expressiveness at the cost of unproved merges,
rejected by [[SPEC-038-lvar-state-kernel#ADR-3801]]). Lasp's stated reason for
leaving threshold reads, that they need a priori knowledge of the carrier and a
monotone queryable value, is met here by the closed algebra and by typing
thresholds against carriers rather than displays
([[SPEC-038-lvar-state-kernel#CON-3801]]). Consequence: the
non-monotone projections stop being an exception; they are snapshots, readable
after a freeze or through a threshold, and the chain's last step is located
exactly.

## ADR-3801: Three tiers of user definition; verified tables yes, code no

Decision: a dialect may define its own lattices and morphisms in two of three
forms, and the third is excluded.

1. *Composition.* Terms over the primitives of
   [[SPEC-038-lvar-state-kernel#CON-3800]]. Any per-act contribution lifts to a
   morphism by the universal property of the powerset, and products, keyed maps
   and composition preserve the lattice laws, so nothing needs checking beyond
   the term's shape.
2. *Finite lattices and tables, verified at installation.* A dialect may declare
   a finite lattice by its elements and join table, a contribution as a table
   from field values to elements, and a post-map as a table from elements to
   scalars ([[SPEC-038-lvar-state-kernel#CON-3803]]). Installation checks the
   lattice laws exhaustively, checks that a post-map marked stable is monotone,
   and bounds the element count by `max-list`, so every check is decidable and
   polynomial ([[SPEC-038-lvar-state-kernel#REQ-3810]]).
3. *Code for a join or a contribution.* Excluded.

Rationale. The determinism of a morphism is conditional on the carrier being a
join-semilattice and on the function distributing over its join. In a trusted
codebase those are obligations a programmer promises: Hydro's `lattices` crate
states that "LatticeOrd must always agree with the Merge function", and "Keep
CALM and CRDT On" leaves the monotonicity of user queries to "type annotations
… along the lines of Blazes" and "formal verification and fuzzing"
([[LVars]]). A dialect arrives as data from any author. A merge that is not
commutative or not idempotent breaks replica agreement silently, which is the
premise of [[SPEC-037-state-kernel-sec]]; unbounded code breaks the R2 bounds
and reopens the undecidability that the first inclusion of the chain closes
([[protocol-model]]). For finite tables the laws are decidable by inspection,
which is the LangSec discipline of recognising and verifying before use; for
code they are not. Tier 2 therefore gives dialect authors Hydro's and BloomL's
expressiveness without their promise.

Alternatives: the previous form of this decision, composition only, which was
simpler but needlessly excluded any carrier the primitives do not spell;
user code with a required test suite, rejected because tests cannot establish
a universal law and the author is untrusted. Consequence: a new primitive still
needs a proof, a new term needs none, and a new finite lattice needs an
installation check whose cost is stated in
[[SPEC-038-lvar-state-kernel#NFR-3800]].

## ADR-3802: Freeze against a concurrent write

Decision: a write concurrent with a freeze is, by default, excluded from the
frozen value and recorded as superseded, following the observed-removal pattern
already used by `lww-map`; a dialect may instead declare `fault`, which joins the
field to ⊤. Rationale: in LVish the concurrent case is an error because the
program is one process; here the two acts are signed and causally related or
not, and the dialect knows whether a late vote is a breach or merely late.
Supersede keeps determinism and attribution; fault keeps LVish's theorem
literal. The default favours progress; it is provisional and owned by the CBCL
maintainer.

## ADR-3803: A conflict top in every lattice

Decision: ⊤ is a member of every carrier and is rendered uniformly as a fault
with evidence. Rationale: the kernel already behaves this way for `initial` and
`bounded-counter` without saying so, and making it explicit turns `initial` from
a revisable display into a monotone one. Consequence: the SEC theorem's case
split becomes "same value or ⊤", which is quasi-determinism.

## ADR-3804: The sixteen heads are abbreviations

Decision: no existing wire form, address or vector changes; the shipped heads
are documented as abbreviations of terms and checked against the term evaluator
differentially. Rationale: [[SPEC-038-lvar-state-kernel#REQ-3807]], and the
Simplicity Ladder: the first slice adds a pure module and tests, no new syntax,
and proves the factorisation claim executably before any surface changes.

## ADR-3805: Read semantics that match the dialect author's intent

Decision: thresholds establish stable successful facts; snapshots describe
current values; conflict is a separate failure with attributable evidence.
This decision was accepted by the CBCL maintainer on 8 November 2026.

A signed net balance is revisable, even when its credits and debits are each
nonnegative. Its threshold SHALL NOT silently read only its credit half.
For an explicitly named gross-credit stream an author may write:

```lisp
(shape credit (require :amount nonnegative))
(state
  (credits (events credit :amount))
  (threshold funded credits (sum 10)))
```

The shape recognizer enforces nonnegativity before admission. A signed
`number` field is unchanged; its sum remains available as a snapshot, and
exact reads are available through [[SPEC-038-lvar-state-kernel#CON-3802]].
Installation rejects a revisable threshold with an explanation pointing to
snapshot, freeze, or an explicitly monotone source, rather than changing the
meaning of the author's term.

`fault` is not an alternative that the author must remember to put in a
threshold. Every threshold first checks its dependency faults. A threshold
that was reached may subsequently fault, but may never silently become pending
or report a different successful element. Hosts retain the history of observed
events; this kernel does not undo external actions and does not establish their
exactly-once execution.

Domain-governed carriers retain raw initializer evidence and contribution
evidence under union. Their displays filter against the initializer and fault
when it conflicts. Conflicting allowed-choice lists must not present a tally
of zero as ordinary business data. Derived fields propagate their source's
fault rather than reducing it to zero or an empty map.

Placement: use the existing shape recognizer for the additive `nonnegative`
type, the existing lattice module for history carriers, and the existing fold
for fault propagation. No host service, custom parser, or new rule head is
needed. Rejected alternatives: ignoring negative amounts, interpreting net
balance as gross credits, choosing a threshold answer at conflict top, and
restricting the merge law to replicas that already share an initializer.
Trace: [[SPEC-038-lvar-state-kernel#REQ-3800]],
[[SPEC-038-lvar-state-kernel#REQ-3802]],
[[SPEC-038-lvar-state-kernel#REQ-3804]].

## ADR-3806: Explicit history terms for closure heads

Status: accepted by the maintainer on 2026-11-08.

Decision: `progress` and `bounded-counter` factor into a raw accepted-history
carrier under union and a native closure projection. The fold uses the same
factored-term path for all installed heads. Domain/dependency faults and freeze
orchestration belong to the common kernel. Protocol-position reconstruction
and resource-DAG validation remain specialized pure algorithms inside the
closure projection; their arithmetic is not replaced with per-act scalar
summation. The independent legacy evaluator remains a differential reference
for conflict-free conformance histories.

Rationale: an absent factorization confused lack of a smaller summarizing
carrier with lack of an LVar interpretation. The identity lift already supplies
the algebra. Explicit terms remove a runtime exception and extend the same
partition, permutation and duplicate-delivery checks to both closure heads.

The LVish implementation provides a useful implementation cross-check:
`verifyFiniteJoin` checks the three join laws; `verifyFiniteGet` checks that a
successful read cannot become blocked or change its successful answer while
allowing an error outcome. Its frozen collection interface distinguishes
freezing from ordered traversal, and `runParThenFreeze` relies on a completion
barrier. CBCL's distributed close remains an explicit causal act; local
quiescence supplies no global completion evidence. The LVish review is a design
reference; any copied or translated implementation retains its BSD-3-Clause
copyright notice, conditions and disclaimer. Reviewed the published
`lvish-1.1.4` sources and the upstream implementation:
[finite join/read checks](https://raw.githubusercontent.com/iu-parfunc/lvars/master/src/lvish/Data/LVar/Internal/Pure.hs),
[frozen traversal](https://raw.githubusercontent.com/iu-parfunc/lvars/master/src/lvish/Data/LVar/Generic/Internal.hs),
[completion barrier](https://raw.githubusercontent.com/iu-parfunc/lvars/master/src/lvish/Control/LVish/DeepFrz.hs).

Fault evidence is a contextual certificate containing the conflicting witness,
not a minimal blame set. Resource faults retain accepted resource facts and
accepted cited context so a later diagnosis cannot erase an earlier witness.
This changes conflicting-history evidence where necessary; conflict-free
conformance observations and all wire addresses remain unchanged.

Trace: [[SPEC-038-lvar-state-kernel#REQ-3800]],
[[SPEC-038-lvar-state-kernel#REQ-3804]],
[[SPEC-038-lvar-state-kernel#REQ-3806]],
[[SPEC-038-lvar-state-kernel#REQ-3808]].

## TEST-3800: Factorisation and morphism law

For every conformance vector in `test-vectors/state/` and every field whose head
factors, (a) the term's displayed value equals the shipped fold's value on the
accepted set, in forward, reversed and duplicated delivery; (b) for the partition
of the accepted set into even and odd positions, and into first and second
halves, `L(A₁ ∪ A₂) = L(A₁) ⊔ L(A₂)`; (c) the two closure heads factor into
history carriers and their native closure projections
from `factor`. Include causally closed, admitted histories with different
openers: joining their raw carriers SHALL equal the carrier of their union,
while conflicting initializer displays and dependent fields SHALL fault with
the opener addresses. Validates REQ-3800, REQ-3801, REQ-3808.

## TEST-3801: Threshold determinism

Property test: for a dialect declaring thresholds over `count`, `set-union`,
nonnegative numeric `events` and `progress`, any permutation and duplication of a
delivery reaches the same element, the element is reached at most once, and a
reached element is never retracted on any non-conflicting superset. On a
conflicting superset the observation SHALL become a fault with evidence,
never pending or another successful element. Validates REQ-3802.

## TEST-3802: Freeze

A `close` verb freezes a `values` field. After `close`, the rendered field
carries `frozen`; a later write that cites `close` is excluded under
`supersede` and faults the field under `fault`; a write concurrent with `close`
is treated per policy; reads before `close` are unmarked snapshots.
Validates REQ-3803.

## TEST-3803: Install rejects compatible thresholds

With `coins` a nonnegative numeric events field, installing
`(threshold t coins (sum 10) (sum 20))` is rejected because the
two elements are comparable; `(threshold t coins (sum 10) fault)` is rejected
because fault is not a successful alternative;
`(threshold t flag #t #t)` is rejected as duplicate; a `count` element against
a `vals` carrier is rejected as mistyped; the check runs in `O(k²)` comparisons.
Validates REQ-3802, NFR-3800.

Core additions: a signed `number` events source and every `counter` are
rejected as sum-threshold sources; a `nonnegative` events source installs and
reaches ten for amounts six and four; its negative write fails recognition
before acceptance; a signed balance still renders ten then nine as a snapshot.
Verify fault-only and mixed successful/fault threshold declarations are
rejected. For a domain initializer conflict, verify reached becomes fault with
the opener evidence, never pending, for every declaration order and delivery.

## TEST-3804: Conflict top

Two distinct openers render `initial` as `fault` with both addresses; a
resource fork renders the same shape; a late write under the `fault` freeze
policy renders the same shape; in each case the fault survives every superset.
A protocol-admitted insufficient-rights fault remains a fault when another
account adds an operation with a missing escrow dependency; the earlier
accepted witnesses remain in its evidence. Missing references may prevent a
ready balance, but cannot suppress independently established faults. Validate
that restoring the early missing-reference return makes this regression fail.
Validates REQ-3804 and REQ-3806.

A `progress` source over a domain-filtered tick verb still observes every
accepted tick. A late domain-excluded tick faults a `fault`-frozen progress read
and its dependent threshold, retaining both addresses; `supersede` lists that
tick as excluded. The ordinary `count` still honors its domain. Resource
operation domains reject at installation. Validates
[[SPEC-038-lvar-state-kernel#REQ-3803]],
[[SPEC-038-lvar-state-kernel#REQ-3806]] and
[[SPEC-038-lvar-state-kernel#REQ-3808]].

The live causal-DAG oracle executes a freeze read proved equal to the existing
Lean `freezeRead`. A separately checked causal rank supplies a compressed
history-length search bound without ordering semantic identities; executable
ancestry, exact cuts, earliest freezers and complete
conflict evidence are connected to their semantic definitions. Native fold
comparisons cover both freeze policies, repeated/concurrent freezers,
multi-parent ancestry, late contributions, raw top faults and unioned raw/freeze
evidence. Missing predecessors and ambiguous identity/keyword inputs reject
at the oracle boundary. Isolated native cut/policy/concurrency/evidence mutations
must fail these comparisons. Generated DAGs are bounded fold inputs; this does
not establish protocol admission or mutable-reader extraction. Validates
[[SPEC-038-lvar-state-kernel#REQ-3803]] and
[[SPEC-038-lvar-state-kernel#REQ-3806]].

The live `events-sum` profile adds a separately frozen event source and derived
sum. Its executable map/error/presentation/freeze adapters refine the semantic
native adapters. Real native cache comparisons include a directed split-cut
case: the source's frozen events sum to 2, while the derived field's own frozen
cut must yield 7. Erasing scope or field from the cache key, evaluating a
dependency at whole history, retaining a source's freeze wrapper, or dropping
its fault must fail the live comparison. The profile covers one derived layer
and bounded integer payloads, not arbitrary graphs or overflow. Validates
[[SPEC-038-lvar-state-kernel#REQ-3803]],
[[SPEC-038-lvar-state-kernel#REQ-3806]] and
[[SPEC-038-lvar-state-kernel#REQ-3809]].

## TEST-3805: Snapshot marking

`state_schema` marks every field that is neither threshold nor frozen as
`snapshot`; immutable context projections are marked `context`; the bindings'
documentation states the host obligation.
Validates REQ-3805.

## TEST-3806: Quasi-determinism in Lean

Build, lint and axiom-audit a theorem that specialises to
`strong_eventual_consistency` when no field reaches ⊤, and that, when a field
reaches ⊤ on one replica, every replica with the conflicting witness accepted
reaches ⊤ with evidence containing that witness. Equal accepted sets yield
equal evidence; complete finite-history delivery yields eventual equality of
the entire observation. Validates REQ-3806.

## TEST-3807: Vectors unchanged

Every vector's addresses, verdicts and rendered state are byte-identical to
`main` before this specification on conflict-free histories, except for members
the vector's dialect explicitly declares. Conflicting initializer/resource
histories render explicit faults and propagate dependent faults under
[[SPEC-038-lvar-state-kernel#REQ-3804]], without requiring a new declaration.
Validates REQ-3807.

## TEST-3808: User-defined lattices

A three-element lattice `{lo, mid, hi}` with the chain join installs and
behaves as `max`; the same table with `(join lo hi mid)` and `(join hi lo hi)`
is rejected as not commutative, naming the pair; a table missing a row is
rejected as not total; a table where `join a (join b c) ≠ join (join a b) c` is
rejected as not associative, naming the triple; a `project stable` table that
maps `mid ↦ 2` and `hi ↦ 1` is rejected as not monotone; the same table without
`stable` installs and is marked snapshot; a lattice of `max-list + 1` elements
is rejected; the installation check completes within the `O(n³)` bound on a
64-element lattice. A field over the accepted lattice passes TEST-3800's
display and morphism checks. Validates REQ-3810, NFR-3800.

The live Lean oracle supplements these finite checks with generated authored
inputs, native installation and actual Rust folds. `StateKernelOracle.lean`
executes the proved reference functions, without consuming expected Rust
outcomes. The property test `state_kernel_oracle` compares installation,
projected values, pending/reached thresholds and fault evidence under forward,
reversed and duplicate delivery. Proptest shrinks mismatches and persists
replay seeds. Directed numeric/Boolean cases and isolated Rust mutations guard
against a vacuous comparison. The bounded profiles exclude domains,
context, resources, protocol admission and canonical diagnostics;
those paths retain their separate obligations. Validates
[[SPEC-038-lvar-state-kernel#REQ-3802]],
[[SPEC-038-lvar-state-kernel#REQ-3804]] and
[[SPEC-038-lvar-state-kernel#REQ-3810]].

## TEST-3809: Context as ordinary kernel data

Core: read the complete map and supported typed paths; verify signing hash,
alias-independent body address, authored name, bounds, role declarations,
thread provenance and actual sealed occupants. Missing roots remain absent;
malformed casts, conflicting roots and wrong pins fault deterministically under
reordering/duplicates. Sealed rosters supply data domains and existing membership
thresholds under normal role admission. Reject unknown paths/roles and unintended
policy-specific forms. Verify schema stability markers, canonical cache exclusion
and install-time cache rebuilding. A frozen context observation includes late
accepted acts even when an application domain excludes them, and cannot hide
later root conflicts. Extending an already-faulted context with a conflicting
root retains the earlier mixed-thread and relevant opener-fork witnesses; roster
projections do not acquire unrelated opener witnesses.
Mutation checks detect bypassed pin validation, missing
stability marking and dropped observation contributors.

The live context profile executes `StateExecutableContext.read`, whose
`read_refinement` theorem equates computed projections and complete enumerable
fault evidence to `StateInstalledContext.nativeRead`. The Rust differential
harness compares every closed context path, sealed roster membership reads,
metadata/schema markers and combined root/mixed-thread/opener witnesses under
forward, reversed and duplicate delivery. Lean context request validation requires
consistent identities, present predecessors and a checked separate causal rank.
Quoted dialect pins cross the strict parser and native message parser before
cast/context evaluation. Canonical hashes and act addresses are normalized only
on exact equality; hash correctness, signature checks and protocol admission
remain outside this profile. Literal parser extraction is not formally proved.
Context freeze/domain composition remains covered by native tests rather than
this live profile. The executable serializer reports depth exhaustion as an
input error instead of truncating an observation. Predicate-set serialization
uses the input-supported roster/frontier identities; support completeness is a
profile boundary rather than a separate proved theorem.
Validates [[SPEC-038-lvar-state-kernel#REQ-3811]].

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `cbcl_core::lattice`: terms, carriers, join, evaluation, display.
- `cbcl_core::state::fold`: unchanged; the existing evaluator.
- Install checks for threshold incompatibility, freeze roles, and the lattice laws of user-defined tables.

### Effectful Shell (orchestrates I/O, calls pure core)
- Hosts and bindings that subscribe to threshold crossings and freezes and fire effects.

### Boundary Contracts (data types crossing the boundary)
- Rendered state JSON with `reached`, `pending`, `frozen` and `fault` members: core → shell.

### Dependency Rule
Dependencies point inward: shell → core. `lattice` imports nothing from any host.

### Enforcement
`no_std + alloc` and `#![forbid(unsafe_code)]` on the crate; the module has no feature-gated I/O.

## Proof obligations and evidence

The Rust implementation includes the shared lattice/history path, stable
thresholds, explicit snapshot/context schema markers, causal freeze reads,
finite user lattices and the generic context map. The core/parser suites and
`scripts/check-lvar-semantics-mutations.py` exercise these behaviours. The
workspace all-target check and core/parser no-default-features check pass.

`StateLift.lean` establishes the lift algebra and per-head invariance;
`StateLVar.lean` covers threshold agreement, domain-fork faults, causal freeze
cuts and witness dissemination over actual replicas. Its
`fault_aware_strong_eventual_consistency` theorem establishes finite-history
agreement of the entire modeled legacy clause, using the resource port's
extensionality premise. `StateContext.lean`
covers immutable typed root projections, conflict persistence and eventual
fault dissemination. `scripts/check-state-lvar-mutations.py` checks that the
concrete proof obligations reject altered fault, cut and root behaviour. The
full Lean build and allowlisted axiom audit pass at this checkpoint.

`StateResource.lean` adds concrete finite certificates for initialization,
recognition, owner forks, foreign links, cycles and closed-cone budget failures.
It proves cone uniqueness, evidence growth and actual-replica dissemination,
with explicit i128 and native-size bounds. `StateResourceTests.lean` checks a
concrete insufficient-rights certificate, no-opener precedence and checked
arithmetic. `StateObservationPlan.lean` adds typed value dependencies, nested
freezes, reached/context tags, dependency-fault-first thresholds and a composed
replica theorem. The mutation harness includes these modules.

`StateResourceNative.lean` proves executable recognition and checked
initialization/operation checks equivalent to their certificate predicates. It
also proves grouped incoming checked arithmetic agrees with a flat fact fold,
including negative starting budgets, given the owner-prefix partition.
`StateResourceSummary.lean` proves successful native record folds have the exact
sequence, cumulative counters and per-recipient transfers of their supplied
prefixes. `StateResourceCache.lean` recovers those prefixes from actual previous
lookups. `StateResourceKahn.lean` and `StateResourceCycle.lean` establish executable
cycle-certificate equivalence and processing of closed components despite
unrelated missing references. `StateResourceCones.lean`, `StateResourceFrontier.lean`
and `StateResourcePartition.lean` reconstruct cones and derive the owner partition.
`StateResourceBudget.lean`, `StateResourceOutgoing.lean` and
`StateResourceLocalBudget.lean` connect actual cached counters, recipient totals
and both checked local-budget sides to that cone. Native representation bounds
discharge selected-total and summary overflow obligations.
`StateResourceWitness.lean` proves per-operation budget rejection iff a supported
finite budget witness exists. `StateResourceMachine.lean` preserves the joint
summary/cone/frontier invariant from empty state over a successful fresh record
schedule. `StateResourceCounters.lean` verifies mutable waiting-map decrements,
ready-queue updates, saturation and structural missing-reference release.
`StateResourceGraph.lean` derives the identity-indexed dependency graph from
recognized operation facts; `StateResourceCoupling.lean` connects readiness to
actual summary and cone availability. `StateResourceRecordBounds.lean` proves
recognized record overflow unreachable. `StateResourceAuthorization.lean` and
`StateResourceWorklist.lean` interleave authorization with those queues and
caches. Their `native_budget_worklist_certificate_iff` theorem proves budget
worklist fault iff an accepted finite budget witness exists under the executable
phase checks, including a closed witness beside unrelated missing references.
Empty allocation recognition and
explicit account spelling are part of the certificate model. Unsupported native
profiles retain their history-independent empty fault evidence; supported
profiles retain contextual accepted evidence.

`StateRuleRefinement.lean` proves the value-level domain/context/derived/freeze
adapters and source-linked closure thresholds agree with their typed plan
interpretations. `StateCountRefinement.lean` supplies a concrete installed
single-domain count source, matches its display to the address carrier, and
proves reached-or-fault stability under accepted-set growth. These adapter and
source-instance refinements do not constitute the complete installed-clause
compilation theorem, and arbitrary source-linked queries are not assumed stable.

`StateResourceAggregate.lean`, `StateResourceAccounting.lean` and
`StateResourceSolvency.lean` connect checked native aggregate folds to the
worklist's actual successful authorizations. Signed intermediates are retained;
final account nonnegativity and bounded conservation are derived. Installed i64
floor/ceiling checks and physical representation bounds discharge every final
aggregate overflow branch. `StateResourceFinalize.lean` and
`StateResourceValidated.lean` compose that result with the budget worklist.
`StateResourcePreflight.lean` and `StateResourceVerifier.lean` then prove
`native_verifier_certificate_iff` for the complete typed classifier and
`native_certificate_read_refinement` for its exact contextual evidence set.
Unsupported profiles retain constant empty evidence. Native fault persistence
is a consequence of that equivalence, rather than a supplied classifier law.

`StateInstalledCompiler.lean` proves ordered installed-IR name resolution and
interpretation equivalent to typed plans, including rejection and completeness.
Its independent readers retain history-indexed dependencies.
`StateInstalledClause.lean` attaches global freeze metadata before compiling
dependencies and connects resource leaves to the verified native classifier.
`StateInstalledLattice.lean` generates display and raw-query carriers from the
same source metadata, checks nonempty distinct non-top incompatible alternatives,
and retains element rendering/decoding consistency.
`StateInstalledLowering.lean` resolves each threshold's strategy from its named
source, invokes native closure query checks, rejects supersede-frozen threshold
sources, and proves whole installed semantic-IR refinement, completeness,
finite-history strong eventual consistency and attributable fault dissemination.
Representation embedding preserves reached/context tags; derived maps consume
frozen payloads and produce snapshot values. Regression and mutation checks
cover these distinctions and late freeze attachment.

`StateResourceCompletion.lean` and `StateResourceReadEquivalence.lean` extend
fault classification to equality of the complete modeled pending/ready/fault
read, including value, rights and headroom under fact permutation. Missing
operation dependencies can still leave a checked history pending; the accepted
root theorem concerns preflight only. The modeled read omits native missing-link
lists, owner tips, diagnostic reasons and serialization.

`StateInstalledLegacy.lean`, `StateInstalledResource.lean`,
`StateInstalledContext.lean` and `StateInstalledDomains.lean` supply concrete
retained-history source factories. Displays and raw queries share the retained
term state. Legacy eligibility rejects revisable member queries; context paths,
cast cardinality/completeness, pins, domain verb/key/source typing and relevant
fault scopes are checked explicitly. Resource snapshots invoke the typed native
verifier and are proved equal to its read on actual accepted history.

`StateFiniteTable.lean` constructs the bounded semilattice from resolved total,
single-valued rows and exhaustive law checks. `StateFiniteProjection.lean`
checks scalar rows, projection totality and stable integer/boolean order,
including top. Contribution rows retain proof of scalar recognition and join
all simultaneous matches. `StateInstalledFinite.lean` resolves authored source
metadata and connects domain/top errors to the exact native writer witness
sets, preserving evidence under diagnostic precedence. `StateFiniteRead.lean`
binds named and stable projected scalar queries to the same raw source state;
its non-top common-upper-state check entails quasi-determinism even when union
enables additional domain-selected contributions. These executable typed
reference checks establish semantics, not equivalence of their traversal costs
or first-error diagnostics with the optimized Rust validators.

Native context regressions additionally cover a later root fault replacing an
earlier mixed-thread or opener-fork diagnostic. Independent fault witnesses
remain in evidence; opener witnesses affect only whole-context, whole-thread
and opener projections. Role-roster projections retain their narrower scope.

`StateAuthoredBindings.lean` binds the complete legacy/context/finite/resource
source inventory and source-relative thresholds, collects domain/lattice
metadata clause-wide, preserves earlier aggregate references, and validates
freeze targets against actual source fields. Its static preparation and freeze
templates isolate history-independent checks from full-observation contributor
specialization. Progress contributors bypass application domains; resource
operation domains reject before execution. Regenerating the same templates on
equal accepted sets yields equal compiled observations.

`StateFreezeGrowth.lean` transfers the same freeze witnesses when both history
and contributor selectors grow. `StateCompiledFreezeGrowth.lean` reflects
literal rule/field compilation to its exact error paths, preserves successful
compilation under observation growth, and proves named whole-clause fault
evidence inclusion plus `eventual_authored_fault` using actual replica witness
dissemination. The latter disseminates the finite source accepted history, not
an extracted minimal witness. `StateFreezeScopes.lean` proves closed-scope
freezer selection, equality of cached global cuts, and
`cached_plan_data_refinement` for globally clear source/freeze paths.
`StateNativeReader.lean` independently evaluates scoped error and value passes
using full-history freeze plans. `native_reader_refinement` proves complete
observation equality, including faults and nested freezes, on closed histories
with unique addresses. This is the functional plan-reader composition;
correspondence to Rust mutable cache entries and dependency lookup remains open.

`StateFiniteUpperCache.lean` proves optional upper-set maxima preserve exactly
non-top numeric witnesses, then proves named/named, mixed and numeric/numeric
compatibility against common successful upper states. Admitted authored scalar
decoding preserves integer and Boolean projection semantics. Its normalized
cached pair and complete admission gates equal the exhaustive finite reference
gates on all inputs. `StateFinitePairLoop.lean` constructs stored projection and
maxima vectors and proves their lookups equal those formulas. Its indexed
unordered early-exit loop equals the reference gate and returns the first
rejected candidate in row-major order, with duplicate precedence and indices
selecting the original authored scalars. These close the modeled cache and
pair-loop semantic obligations. Typed extraction and integration into R7,
formatted diagnostics, and allocation/runtime cost correspondence remain
separate boundaries; the model decodes per pair while Rust stores a reads
vector. No cache complexity theorem is claimed.

`StateInstalledRecognition.lean` proves exact lowerer acceptance from the
modeled metadata, source policy and backward-reference checks. Authored
preparation now performs those checks before returning success;
`prepared_compiler_complete` constructs compiled plans without separately
assuming metadata validity or reference well-formedness.
`preparation_preserves_compilation` proves every previous successful plan and
rejection is preserved. `StateAuthoredCompletion.lean` composes successful
preparation through concrete readers and the functional cached reader,
including faults, and preserves complete observations on equal accepted sets.
These reference validators remain `noncomputable` Lean definitions; extraction
to the actual native installer and mutable Rust reader is not claimed.

A native regression found that a data-domain-excluded tick could evade progress
freeze evidence although progress reads raw history. The Rust selector and
concrete authored footprint now retain every accepted tick of the selected
verb. Under `fault`, the frozen source and dependent reached threshold fault
with freezer/tick evidence; under `supersede`, the tick appears in exclusion
metadata. Restoring domain filtering makes the named regression fail. Resource
operations already prohibit such domains at installation; that rejection is
also modeled in authored preparation.

`StateMemoizedReader.lean` adds an operational cache model with exact
`(scope, field)` lookup keys, dynamically branching dependency continuations,
cache insertion after completion and shared state across top-level requests.
Its well-founded uncached recursion constructs the independent reference
meaning; `read_refinement` preserves valid entries, and
`native_reads_refinement` starts from the empty cache rather than assuming
correct cached values. Native orchestration requests earlier dependencies in
the current scope, unwraps their frozen payloads, checks combined faults before
historical redirection, and requests the same field at its globally planned
cut before adding the current scope's metadata.

`StateReaderIndices.lean` derives unique field names and backward scoping from
successful installed-clause compilation. `compiled_native_cache` constructs the
numeric dependency ranking from concrete field positions and composes it with
the operational cache theorem. The secondary rank decreases when a field
redirects into its own planned cut; it does not require scope IDs to be ordered.
At that layer, typed dependency-to-IR-reference extraction is a premise. The
concrete authored-dependency construction below discharges it for the recognized
source inventory. Typed normal/fault/wrapper operations remain separate
boundaries. This orchestration models known compiled fields: Rust's unknown-field
branch returns absent without inserting a cache entry. The association-list
cache proves lookup/result semantics, not ordered-map representation or cost.
Executable witnesses distinguish source sum 2 from derived cut value 7 and
preserve terminal witness lists without reading the faulted field's cut.

`StateAuthoredDependencies.lean` derives the exact native field dependency
inventory from original concrete declarations. `bind_references` proves both
preservation and absence of spurious references for every source factory:
histogram and sum each retain their authored source; other heads have no field
dependency. The result survives auxiliary entries, declaration lowering,
observation specialization and source-relative resolution. Successful preparation
constructs the installed field clause, its namespace and cache ordering instead
of accepting a detached dependency-to-IR relation.

`StateScopePool.lean` constructs scope zero and interned causal-cut scopes from
typed freeze declarations and full accepted history. Repeated freezer identities
reuse indices; appending cuts preserves earlier lookups. Root selection removes
duplicate deliveries, accepts exactly a unique semantic earliest freezer, and
returns no scope for absent or concurrent roots. Cut values refine the proved
executable causal cut. Normalization preserves the accepted set and derives
unique addresses under content-identity consistency. The active callback tests
freezer membership in the actual indexed scope; it is not supplied by a caller.
`prepared_scoped_cache` composes the scope certificate with prepared dependencies
and operational cache execution under ranked, consistent delivery premises.

At that layer, native normal-value, combined-fault and presentation leaves are
supplied operations. The fixed value construction below instantiates them and
proves their local compiled-source equations. Literal native topological frontier
construction, address deduplication representation and map/vector layout/order
remain separate extraction boundaries. The scope model uses full-act duplicate
removal under identity consistency; it does not establish Rust allocation order
or performance. A repeated-freezer executable regression distinguishes duplicate
delivery from competing roots; a mutation removing deduplication fails it.

`StateReaderValues.lean` constructs typed normal, fault and frozen-presentation
operations from resolved installed rules and the actual indexed scope pool.
Primitive sources call `sourceRead` at that scope; histogram/sum consume the
completed dependency payload; full-observation freeze errors are unioned with
normal source errors before historical reads. Frozen wrappers and exclusions
come from the selected accepted freezer and current scoped contributors.
`prepared_fixed_cache` combines prepared compilation, scope construction and
memoization with these fixed operations, without caller-supplied leaf classifiers.

`source_scoped_refinement` and `derived_scoped_refinement` establish local
complete-observation equations to `StateNativeReader`. `freeze_error_refinement`
retains both witness sets, and `cached_freeze_scoped` establishes the complete
cached freeze adapter's value/error equation on closed contained scopes.
`scoped_clear` and `cut_clear` ensure historical redirection cannot conceal a
source fault. Prepared original source fields are proved to lie in the supported
primitive/derived inventory; threshold-output entries remain separate.

`StateReaderReachability.lean` constructs the full native initial request list,
including threshold sources rather than threshold-output names. Successful
preparation proves aggregate and threshold sources are original source fields.
Every dependency continuation preserves this inventory and allocated scopes,
including value-dependent and fault-dependent branches. `prepared_reachable_cache`
combines fixed execution, scope soundness, cache validity and provenance; every
stored key retrieves an allocated history and an exactly looked-up supported
primitive/derived rule. Invalid-scope and unsupported-IR helper fallbacks are
therefore excluded from these admitted requests. A concrete context/count/
threshold/freeze fixture establishes preparation and request admission without
assuming that the installation succeeds.

`StateCompiledFieldEquations.lean` derives exact lookup equations from successful
installed compilation. Every rule resolves the same earlier source plan in the
completed unique dictionary; source and derived fields retain their attached
freeze decoration. The concrete operational dependency option equals the entire
resolved reference inventory, including the no-dependency case.
`prepared_body_normal` identifies every admitted field's normal body step with
the actual bare compiled scoped plan. Own-freeze finishing is kept explicit.

`prepared_unfrozen_body` closes the complete body equation for a field without
its own freeze, including faults and derived reads of separately frozen source
plans. `prepared_no_freeze_reference` and `prepared_no_freeze_cache` establish
recursive reference and native initial field-request transcript/cache equality
to the compiled meanings for successfully prepared clauses with no freezes.
The transcript includes threshold source reads; it is not a theorem about the
subsequent threshold-output adaptation or serialized clause rendering. Concrete
fixtures retain a supersede freeze inside a derived source and construct an
admitted threshold-bearing clause with empty freeze metadata.

`StateScopeProperties.lean` constructs closed, contained, address-unique allocated
scopes and relates executable freezer selection, cut indices, activity and
excluded evidence to the semantic plan. `StateFrozenBodyEquations.lean` closes
the successful own-freeze finishing equation, including absent roots, inactive
roots, same-scope cuts and historical recursive reads. Fault and data cases
compose in `prepared_body_equation`; `prepared_reference_equivalence` and
`prepared_cache_equivalence` establish the independent recursive reference and
complete initial source-request transcript/cache equality for prepared clauses
with freezes. Concrete fixtures construct incomparable cuts and a prepared
context/count/threshold/freeze clause.

These results require content-consistent histories admitting a separate causal
rank. `StateFiniteCausalRank.lean` compresses any such rank into counts below
its values, proving strict decrease and a bound below history length even with
duplicate delivery. `StateExecutableFreeze.ancestor` uses history-length fuel;
its exact ancestry/cut proofs and the actual scope, cache and output compiler
pipeline preserve semantic addresses and arbitrary delivery order. No sorting
or address renumbering is needed for execution.

`StateCausalRank.lean` constructs a candidate topological order and independently
recognizes its vertex coverage and edge order. `causalCheck_sound` constructs the
rank premise from successful recognition. `StateCausalCheckComplete.lean` proves
that the actual Kahn implementation constructs exact vertex coverage, unique
addresses and a checked edge order for every content-consistent ranked history.
`causalCheck_iff` establishes recognition equivalence with a separate causal rank;
`causalCheck_setEq` proves recognition invariant under reordered and duplicate
delivery. These statements concern edges between present vertices. Predecessor
closure remains a separate validator check, with a fixture distinguishing the
two obligations. Freeze and context live-oracle validators use this checker;
generated vertex labels decrease along edges, with reversed and duplicate delivery.
The authored integration fixture constructs complete compiled/cache outputs for
a descending-address, reversed, duplicated history. Rank extraction from literal
native admission and cryptographic address representation remain boundaries.
`StateThresholdDispatch.lean` now proves that allocated raw-threshold scope is
exactly the semantic selected-freezer cut. Completed source faults are preserved;
healthy raw reads do not require a displayed payload or full-history locality.
`installedAt` takes policies, tests and carriers from the named installed source,
covering native closure, factored raw-term and checked finite-lattice queries.

`StatePreparedOutputs.lean` walks the actual prepared declarations with evolving
source definitions. `evaluate_complete` constructs successful outputs from
successful lowering, excluding equality caused by two failed output walks.
`prepared_cache_outputs` connects the actual empty-cache source transcript to a
common successful output list, composing source observations, source-owned
threshold policies and exact raw cuts in declaration order. A concrete authored
context/count/threshold/freeze fixture constructs both installation and outputs.

`StateOutputCompiler.lean` compiles source-owned closure, raw-term and checked
finite query policies into a closed output-code inventory. Each instruction
captures its complete original source plan; the program retains the clause's
freeze metadata. `compile_outputs_refinement` relates that code to independent
cut-scoped output execution. `authored_compiler_refinement` constructs successful
compiled output code from actual preparation and connects its complete vector
to the actual empty-cache source transcript and output adapter.

Authored preparation specializes source and contributor metadata to an
observation history. `CompiledObservation` retains that history and its public
`observe` takes no replacement history; history growth requires fresh preparation.
The concrete compiler fixture constructs preparation, code and cache/output
execution rather than assuming them. Older generic full-history `thresholdRaw`
plans remain source-dictionary/checking machinery; they are not emitted as native
output instructions, and no equivalence with their raw-history output semantics
is asserted. A low-level supersede fixture retains the full-history versus
cut-scoped threshold distinction; it explicitly cannot install a threshold over
that revisable source. A separate admitted fault-policy regression installs an
actual dialect and runs AdmissionMonitor: a domain initializer outside a
freezer's cone must produce a fault with initializer/freezer evidence, preserving
the earlier successful threshold as success-or-fault. Metadata-root references
can satisfy an alternative `begin` predecessor, so opener-only declarations do
not imply that every writer descends from the opener.

Domain-filtered freeze footprints retain both eligible writers and all applicable
domain sources: matching initializer acts and sealed-roster roots, including
malformed or currently noncontributing source evidence. These are dependencies
of the field's retained carrier. Fault-policy freezes expose any such evidence
outside their cone; superseding freezes record its exclusion.
`StateDomainSupportLocality.lean` proves that healthy fault-policy cuts preserve
exact allowed sets and selected writers for multiple initializer and roster
domains. Its count growth and `count_success_at_cut` theorems connect earlier
count thresholds to that equality without assuming business-opener dominance.
Fixtures construct mixed domains with descending addresses and reverse/duplicate
deliveries, and an explicit branch missing the opener produces a fault.

`StateOpenerLocality.lean` separately derives opener ancestry from a checked
business-predecessor condition and causal rank. Its conditional uniqueness and
locality results remain valid, but that structural check is not inferred from
literal R5/R6 admission and is not required by the domain-support proof above.
`StateFiniteFreezePolicy.lean` composes that selected-history equality with the
actual finite source's state, closed query admission, upward reach and pair
compatibility checks. For every admitted alternative list, a prior successful
finite query remains the same successful answer or faults after growth and an
exact fault-policy freeze. The proof observes the concrete frozen finite source
plan and derives guard clarity and non-top state; neither healthy-source status
nor raw-state equality is supplied as a premise. `output_success_or_fault`
connects this result to compiled query code, normalization, unique-root selection
and the public output adapter. Fixtures compute a checked three-element table,
non-bottom prior success, mixed initializer/roster domains, reverse/duplicate
delivery and the bypassed-initializer fault.

`StateFiniteOutputStability.lean` generalizes the composition over optional
fault-freeze declarations and every actual root-selection outcome. Unfrozen and
unselected-root reads use normalized full history; selected roots use the exact
cut. The observed source retains all domain/top and freeze guards, so concurrent
earliest freezers fault even when the unique-root selector returns none.
`output_success_or_fault` no longer requires a selected root; `output_reached`
proves actual success when the complete source is clear. Fixtures establish
emitted success without a freeze declaration and while awaiting a freezer, and
an emitted fault under concurrent closes, including the absent-root checks.

`installed_threshold_success_or_fault` also derives the final guarded source
lookup from the original finite source rule and successful installed-field
compilation. It invokes the actual one-declaration output compiler and permits
other fields and freeze declarations in the same clause. Its fixture constructs
the final dictionary before compiling the threshold; no compiled source-plan
lookup is assumed.

`StateAuthoredSourceProvenance.lean` recovers the finite source identifications
from successful authored preparation: actual domain/table resolution, successful
field binding and finite factory result, the stored source-owned definition,
and the final binding used by freeze templates. Namespace uniqueness ties that
binding to the original authored finite field. The threshold stability gate
supplies the optional fault-policy freeze; resolved source-rule and final guarded
source-plan lookup follow from actual resolution and compilation.
`authored_finite_plan` constructs source compilation and the exact final plan
without requiring a resolved rule, table, finite field, freeze identity or
compiled dictionary as premises. The fixture installs mixed initializer/roster
domains, a forward initializer reference and late freeze metadata, and rejects
the same threshold with a supersede freeze.

`StateAuthoredOutputProvenance.lean` follows the actual ordered output compiler's
evolving source definitions. Validated name uniqueness ties a threshold's
source definition to the original finite field, and successful one-declaration
compilation derives the source-owned alternative check and emitted raw-query
code. Every original declaration is connected to an actual occurrence in the
complete emitted code list.

`StateAuthoredFiniteStability.authored_program_stability` composes those results
with source/freeze provenance, normalization and the all-root finite stability
proof. Starting from successful authored preparation, literal finite-field and
threshold membership, and a ranked content-consistent typed history, it
constructs the complete actual `compileAuthored` program. For the recovered
finite field, any earlier native finite-test success survives accepted growth
as the same named reached output or a named fault in that program's actual
observation vector. Query admission, successful output compilation, source-policy
lookup and emitted output membership are derived rather than supplied.
Fixtures construct the complete authored program and a separate complete output
walk whose raw query actually reaches despite an unrelated displayed payload.

`StateCompiledFiniteInversion.lean` recovers native finite-test success from an
actual reached compiled output. The complete ordered output-name vector
identifies the unique threshold occurrence. Raw-query success recovers its
declared alternative and native scope test; actual observed source guards
exclude full-history top, so scope containment and upward reach recover native
full-history success. Equal stored finite definitions yield equal native tests,
connecting separately recovered factory witnesses.

`StateAuthoredFinitePreservation.successive_compiled` applies that inversion to
successive actual `compileAuthored` observations. For the same successfully
prepared finite threshold and ranked content-consistent typed histories related
by accepted-set growth, a named reached result in the earlier program stays the
same named reached result or becomes a named fault in the later program. Neither
earlier native success nor query membership is an external premise. The
fixtures invert a concrete reached waiting-freezer output and construct both
authored programs before specializing the preservation implication.

The same module's `quasi_determinism` composes successive preservation for two
actual compiled observations. If they reach distinct alternatives of the same
finite threshold, every ranked content-consistent compiled joint history that
contains both accepted sets exposes that named threshold as a fault. Validated
output-name uniqueness excludes two distinct reached results in the joint
program. This proves the finite-policy quasi-determinism consequence through
actual authored compilation and program observations.

`StateNativeDataPolicies.lean` connects the actual count/existence kernel
projections and source-owned query policies to emitted raw-query code. Count
canonicalization identifies native count with the cardinality of distinct
selected acts, without a duplicate-free delivery-list premise; existence uses
the same domain-aware selection. `StateNativeDataFreeze.lean` reuses installed
source-plan decoration and derives selected-history equality from the actual
observed freeze error channel for every root-selection outcome. Its count and
existence output theorems preserve an earlier cardinality/nonempty predicate or
expose an actual source fault after growth. Healthy source status, root selection
and locality are not supplied as premises. Fixtures cover mixed initializer and
roster domains, reverse/duplicate delivery, raw queries with pending displayed
payloads, oversized count rejection and constructed frozen count output.

`StateAuthoredDataProvenance.lean` derives the count/existence binding, guarded
source plan and dependency footprint from actual authored preparation. The
proof-only head inventory maps directly to existing rule and kernel expression
constructors; it adds no dialect syntax or source callbacks. The stable-source
installation gate supplies optional fault-freeze metadata.
`StateAuthoredDataOutputs.lean` recovers real emitted instructions and source-owned
query code from the complete compiler, derives count-bound admission, reconciles
normalization, and transfers the factory results to actual named program outputs.

`StateAuthoredDataPreservation.count_successive` and `exists_successive` invert
earlier named reached results in actual compiled observation vectors. Native
scope success lifts to full-history cardinality/nonempty success and then
preserves the same named result or a named fault in the later actual compiled
program. Prior native predicates, detached policy lookups and successful code
walks are not external premises. These results cover singleton count-bound and
singleton true-existence thresholds, with the same prepared dialect and ranked
content-consistent histories related by accepted-set growth. Fixtures install
both policies with mixed domains, a forward initializer and late freezes,
construct both compiled programs, verify the earlier selected cardinality is
one, and specialize preservation conditional on the earlier compiled reached
results. They also compute supersede rejection; they do not assert those earlier
reached results for the complete authored fixture.

`StateNativeMembership.lean` connects set-union membership to the actual kernel
projection of whole selected field values. It does not flatten list-valued
fields or discard superseded values. Source-owned query code tests the raw kernel state independently of its displayed
payload; the authored proof derives scalar admission from successful query
compilation. Witness growth and the observed freeze error channel establish
factory-level membership preservation for every freezer-root outcome.
`StateAuthoredMembership.successive_compiled` composes the shared authored
provenance/output path and inversion from an earlier actual named reached result.
A singleton scalar-member threshold stays the same named reached result or a
named fault in the later actual compiled vector, for accepted-set growth between
ranked content-consistent typed histories. Native membership and detached policy
lookups are not external premises.

Membership fixtures compute reverse/duplicate native success and emitted query
success with a pending payload, reject structured queries and supersede freezes,
and construct both authored programs with count/existence and mixed domains.
The earlier native witness is computed; the preservation implication remains
conditional on an earlier compiled reached result, which the complete authored
fixture does not assert.

`StateEventMapKernel.lean` derives the actual address-keyed event map's source
writers and signer/value cells from map correctness and address-content
consistency. The proof does not assume a clock winner or a projected cell.
Canonical history and domain selection preserve that consistency, giving exact
agreement between the kernel event-member test and selected native field
membership. `StateNativeEventMembership.lean` connects this equality to the
source-owned query compiler and every outcome of the fault-freeze root selector.
`StateAuthoredEventMembership.successive_compiled` then derives admission,
source provenance and earlier native success from actual authored compilation
and its named reached output. Under accepted-set growth between ranked,
content-consistent typed histories, a singleton scalar event-member threshold
remains the same named reached output or becomes a named fault. Neither a prior
native predicate nor a detached policy lookup is an external premise.

Event fixtures compute distinct address entries with equal payloads and retained
signers, duplicate-safe native membership, query success from a pending payload,
and rejection of structured members and supersede freezes. The alternate-signer
identity fixture is a low-level typed-history example, not a protocol-admission
trace. The complete authored fixture constructs both programs with mixed domains
and specializes preservation conditional on earlier reached membership; it does
not assert that antecedent.

`StateEventMapTotal.lean` proves that supported event keys enumerate the unique
present-field writers' addresses, and that the actual map aggregate equals
`sumField` over source writers. Missing fields and nonnumeric payloads contribute
zero; equal numeric payloads at different addresses contribute independently.
The `native_sum` theorem carries this exact total through canonical history and
domain selection into the actual kernel sum test, under the store's unique-address
invariant. Arithmetic fixtures include equal positives, a negative, a missing
field, a nonnumeric field and an unrelated verb, and compute both the exact
threshold boundary and the next pending bound. These are typed arithmetic
fixtures, not protocol-admission traces or nonnegative stability evidence.
`StateNativeEventSum.lean` connects this total to actual source-owned sum-query
compilation with its required signed bound and mandatory nonnegative shape
policy. Its factory theorem covers all fault-freeze root outcomes. The
`StateAuthoredEventSum.successive_compiled` theorem composes actual authored
source provenance, bound/shape-policy admission, emitted instructions and earlier named-output inversion into
later reached-or-fault preservation. Earlier totals use normalized histories so
repeated delivery adds no weight. This result requires actual nonnegative
amounts for accepted later writers as an explicit premise, separately from
installation's shape-policy metadata; it does not yet derive that premise from
protocol admission. Sum fixtures check bounded shaped preparation, rejection of
missing shapes, an out-of-range bound and supersede freezes, computed per-writer
nonnegativity, and emitted query success from a pending payload. They exercise
typed installation and raw-query execution, not a concrete successive
whole-program trace or native admission/extraction correspondence.

`StateNonnegativeAdmission.lean` makes the necessary mandatory/nonnegative
shape-stage projection executable over expanded S-expressions. Lookup stops at
the first matching top-level keyword, including a dangling match. With mandatory nonnegative
metadata, successful checks for all matching recognized writer shapes yield a present nonnegative
numeric atom. `NumericExtraction` explicitly relates that atom to the typed
state field; `checked_history` derives the amount premise, and
`successive_compiled` composes it with actual authored sum preservation.
Concrete fixtures prove both projected checks and extraction for their expanded
writer, and distinguish duplicate keyword order, missing values and quoted
numerals. The live `nonnegative-shape` oracle compares these executable Lean
checks with Rust's actual `ShapeConstraint::check` on the corresponding
require/optional rules, using tagged expanded-message trees that preserve scalar
kinds. It covers the recognized mandatory/nonnegative projection, not general
child/depth/type validation or the strict wire grammar. Full native admission
implying the projected checks, and faithful extraction for every native accepted
message, remain separate proof boundaries.

`StateAuthoredSumTrace.successive_trace` supplies a concrete successive
full-program sum trace. Static preparation and both complete compiled programs
are constructed. Its earlier named `funded` reached output follows from the
actual emitted query and a computed native total, without an earlier-output
premise. The later reversed, duplicate-delivery history has computed shape
checks, proved numeric extraction and normalized total seven; checked-shape
authored preservation then proves its actual later named reached-or-fault
result. This concrete fixture has no freeze declaration and does not assert
native protocol admission. The generic factory/preservation theorems above
retain their all-root fault-freeze scope.

`StateProgressStore.lean` reconstructs causal address lookup from the retained
accepted-act carrier and an immutable per-act evidence decoder. Lookup provenance
and content consistency derive `Repeat.Extends` under accepted-history growth;
no whole-history store-monotonicity callback is supplied. Equal accepted sets
produce equal stores, and consistent histories agree with executable list lookup.
The `context` constructor installs that reconstruction into the actual kernel
context. `kernel_value`, `kernel_test` and `kernel_test_stable` connect actual
domain-aware kernel progress to the existing single-verb resolver's monotonicity.
`compiled_query` proves the existing progress source emits its closure-query
strategy over the computed kernel display, rather than raw query dispatch.
Fixtures compute two then three causal positions, exclude foreign-thread evidence,
avoid inflation from competing and duplicate acts, leave missing ancestry at
zero, and prove actual kernel/closure-query success. Their evidence decoder is
an explicit typed fixture convention; it does not establish native thread/cause
parsing or general repeat-body refinement. The result applies to contexts built
with this history-backed constructor, not arbitrary `Context.causal` functions.
`StateProgressLocality.lean` transfers actual single-verb causal-position
witnesses under verb-restricted history inclusion, rather than requiring every
accepted act inside a freeze cut. The immutable evidence decoder must preserve
each act's source verb. `StateProgressFreeze.healthy_payload` derives the
actual displayed full/cut scope from the observed error channel and the existing
freeze reader, including no-root and selected-root outcomes. Healthy fault
freezes retain every contributing-verb act. `success_or_fault` combines that
scope with causal witness transfer and the actual source-owned compiled closure
query, proving its observed output stays the same reached result or becomes an
actual source fault, for arbitrary optional fault-freeze declarations and global
dispatch metadata. It does not assume a selected root, healthy final payload or
progress-locality equation. Fixtures compute semantic freeze health from the
executable conflict checker, prove an exact cut that drops an unrelated act,
and specialize factory preservation from computed earlier progress. They do not
establish complete authored-program execution.
Full authored progress source/freeze provenance, earlier-output inversion and
successive complete-observation composition remain open.

Full admission/extraction correspondence, authored closure progress composition
and native installation correspondence remain separate obligations at the typed
authored boundary.
Literal Rust value representation and public serialized
rendering remain separate boundaries. Helpers remain total outside the admitted
request domain, which does not model Rust's indexing or unknown-field no-insert
branch.

These theorems operate at explicit typed boundaries. They do not prove Rust
source-code extraction, canonical rendering order, diagnostics, or wire parsing.
The installed semantic IR still receives native closure implementations and
recognized immutable metadata as leaf parameters. The authored lowering above still needs complete native installation-gate
correspondence, literal finite-validator extraction/integration correspondence, and composition with
the literal Rust scoped/memoized reader. The functional cached plan-reader
composition is proved, including faulted reads. Typed metadata extraction must
preserve native scalar distinctions, including quoted strings versus symbols.
The finite live-oracle profile now generates real bare symbols alongside
same-spelling strings and rejects authored symbolic contribution/projection
literals. Its bounded tagged-symbol adapter retains a non-scalar value;
`row_literal_not_list` and `row_ignores_opaque` prove that value cannot match a
verified scalar row. The directed bottom/pending case and a native mutation
that converts symbols to strings test the actual contribution distinction.
This adapter does not establish general metadata extraction or protocol admission;
other live profiles retain their stated scalar contracts.
Generic IR correctness and individual factories are not evidence that this full
literal source binding and composition theorem is complete. The
legacy resource closure port also remains separate from the new concrete
native-certificate bridge.

[[SPEC-038-lvar-state-kernel#TEST-3806]] remains partial at those literal
installation, admission, wire-proof and renderer boundaries. Context pin tests
and the live oracle exercise the strict wire parser using quoted digest strings.
[[BUG-006-envelope-wire-form-unparseable-by-the-real-parser]] remains open for
its envelope and suite-qualified key cases; the dialect-pin context path no
longer relies on the lax parser.
The specification stays `draft` until those acceptance obligations are resolved.

## Changelog

- 0.3.0 (2026-11-08): maintainer requested the read-only dialect/thread context
  map as ordinary kernel input, keeping policy-specific quorum forms outside
  that primitive. Added
  [[SPEC-038-lvar-state-kernel#REQ-3811]] and
  [[SPEC-038-lvar-state-kernel#CON-3804]].

- 0.2.2 (2026-11-08): maintainer selected explicit history-backed LVar terms
  for progress and escrow, sharing the kernel path while retaining native
  closure algorithms ([[SPEC-038-lvar-state-kernel#ADR-3806]]). Reviewed LVish's
  finite-read stability checks, frozen traversal, and completion barrier.

- 0.2.1 (2026-11-08): maintainer selected documenting the current implementation
  cost bounds under [[SPEC-038-lvar-state-kernel#NFR-3800]], including ordered
  collections, scoped freeze reads and concurrent-freeze witness collection.
  Threshold pair checks and finite-table law verification retain their separate
  installation bounds.

- 0.2.0 (2026-11-08): maintainer accepted
  [[SPEC-038-lvar-state-kernel#ADR-3805]] after reviewing signed-sum retraction,
  conflict-top threshold ambiguity, and the admitted-history domain union
  counterexample. Stable facts, snapshots and faults have distinct author-facing
  meanings; full carrier merge evidence is preserved. Implementation and proof
  acceptance must be checked against this version.
