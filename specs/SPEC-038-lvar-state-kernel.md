---
id: SPEC-038
title: LVar state kernel
status: draft
version: 0.2.1
last-updated: 2026-11-08
---

# LVar state kernel

## Orientation

Intent: an LVar state kernel. Each state field is a lattice variable in the
sense of [[LVars]], written only by joining the contributions of
authenticated, admitted acts, read only through threshold reads or after an
attributable freeze, and quasi-deterministic: replicas with equal accepted
sets observe equal values, and any two replicas observe either the same value
or an attributable conflict. This restates the R7 kernel of
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

Metaphor: a notice board. Anyone with standing may pin a notice; nothing is
ever unpinned; a reader may ask "has at least this been pinned?" and get a
yes that never becomes a no; and the chair may seal the board, after which the
whole board can be read exactly and a late notice is a breach, not an edit.

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

Open: freeze concurrency policy default (owner: CBCL maintainer, decided
provisionally in ADR-3802); whether `progress` and `bounded-counter` get a shared
closure combinator or stay as two primitives (owner: CBCL maintainer, see
REQ-3808); sequence lattices are out of scope (recorded, not deferred).

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

A rendered field value that is neither a reached threshold nor frozen SHALL be
marked as a snapshot in the state schema, and the host documentation SHALL
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
threshold alternatives. Whether they share one closure
combinator is open.
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
`factor(&Rule) -> Option<Factored>` (`None` for the two closure heads), an
evaluator `evaluate(&Factored, &Ctx, done) -> (L, Value)`, and `L::join`.

Grammar of terms (abstract; no new wire syntax in this contract):

```text
term         := lift(select+, contribute)            ; join over selected acts
              | pair(term, term)
contribute   := flag | address | field(key) | entry(key) | amount(key)
              | clocked(value-key, clock-key)        ; chain under (hlc, signer, address)
              | write(group) | replaced(group)        ; the W and R halves of supersession
              | sole(key)                             ; initial: ⊥ | one | ⊤
group        := none | signer | field(key)
select       := (verb, raw?)                          ; raw ignores domain filters
post         := identity | size | difference
              | current(post) | group-by(group, post) | pick-lww(value-key, clock-key)
              | distinct(key) | histogram(earlier) | sum(earlier)
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

## TEST-3800: Factorisation and morphism law

For every conformance vector in `test-vectors/state/` and every field whose head
factors, (a) the term's displayed value equals the shipped fold's value on the
accepted set, in forward, reversed and duplicated delivery; (b) for the partition
of the accepted set into even and odd positions, and into first and second
halves, `L(A₁ ∪ A₂) = L(A₁) ⊔ L(A₂)`; (c) the two closure heads report `None`
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
Validates REQ-3804.

## TEST-3805: Snapshot marking

`state_schema` marks every field that is neither threshold nor frozen as
`snapshot`; the bindings' documentation states the host obligation.
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

First slice: `lattice.rs` and TEST-3800 (this branch). Threshold, freeze, ⊤ and
the Lean theorems follow the plan in [[IMPL-030-lvar-state-kernel]]. Nothing
in this specification is claimed as proved until the corresponding TEST reports
it; the status above is `draft` for that reason.

## Changelog

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
