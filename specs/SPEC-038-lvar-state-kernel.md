---
id: SPEC-038
title: The state kernel as a store of lattice variables
status: draft
version: 0.1.0
last-updated: 2026-11-07
---

# The state kernel as a store of lattice variables

## Orientation

Intent: restate the R7 state kernel of [[SPEC-019-state-rules]] as a store of
lattice variables in the sense of [[LVars]], so that every state field is a
term in one closed lattice algebra, every observation is either a threshold
read or a read after a freeze, and the kernel's guarantee is
quasi-determinism: replicas with equal accepted sets observe equal values,
and any two replicas observe either the same value or an attributable fault.
The named failure is **a displayed value that an application acts on as if it
were final when the accepted set can still revise it**. Today the fold is a
set function but says nothing about which of its outputs may be acted on; the
host decides, and the guarantee stops at the fold.

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
                   │ stable: never retracted       │   │ or Violation (ADR-3802)      │
                   └──────────────────────────────┘   └──────────────────────────────┘
                     only these two reads reach the execution layer; a bare
                     projection of σ_F is a snapshot (REQ-3805)
   arrows point inward: the pure kernel never reads the host; the host reads it
```

Decisions: [[SPEC-038-lvar-state-kernel#ADR-3800]] LVars as the kernel model ·
[[SPEC-038-lvar-state-kernel#ADR-3801]] a closed algebra, no user merge functions ·
[[SPEC-038-lvar-state-kernel#ADR-3802]] freeze against a concurrent write: supersede by
default, fault by declaration · [[SPEC-038-lvar-state-kernel#ADR-3803]] a conflict top in
every lattice · [[SPEC-038-lvar-state-kernel#ADR-3804]] the sixteen heads stay as
abbreviations, no wire change.

Load-bearing: [[SPEC-038-lvar-state-kernel#REQ-3800]] every field is a term ·
[[SPEC-038-lvar-state-kernel#REQ-3809]] derived fields over the product, contributions never read revisable fields ·
[[SPEC-038-lvar-state-kernel#REQ-3802]] threshold reads ·
[[SPEC-038-lvar-state-kernel#REQ-3803]] freeze · [[SPEC-038-lvar-state-kernel#REQ-3806]]
quasi-determinism · [[SPEC-038-lvar-state-kernel#NFR-3800]] linear cost.

Open: freeze concurrency policy default (owner: CBCL maintainer, decided
provisionally in ADR-3802); whether `progress` and `bounded-counter` get a shared
closure combinator or stay as two primitives (owner: CBCL maintainer, see
REQ-3808); sequence lattices are out of scope (recorded, not deferred).

Detail: [[SPEC-019-state-rules]] for the fold this restates;
[[SPEC-036-state-kernel-correctness]] and [[SPEC-037-state-kernel-sec]] for the
theorems this subsumes; [[IMPL-030-lvar-state-kernel]] for the plan;
[[protocol-model]] for the refinement chain this kernel sits at the end of.

## Amendment Channels

This specification authorises a new pure module in `cbcl-core` that denotes
existing rules as lattice terms and is checked against the shipped fold, two
new optional state-clause forms (`threshold`, `freeze`), a conflict marker in
rendered fields, and new Lean theorems. It does not authorise changes to
addresses, to the admission monitor, to the verdict algebra of
[[SPEC-003-verification-lattice]], or to the wire form of any existing clause.
Any such change is a separate specification.

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
`bounded-counter`) are monotone closures over cited acts; and `initial` is a
morphism into a lattice with a conflict top whose displayed value is retracted
on conflict. This specification makes that structure explicit and adds the two
reads LVars require.

## REQ-3800: Every field denotes a lattice term

Every state field SHALL denote a term of the closed lattice algebra of
[[SPEC-038-lvar-state-kernel#CON-3800]]: a selector on accepted acts, a per-act
contribution `g` into a lattice carrier, the join over the selected acts, and a
post-map to the displayed value. The join half of every term SHALL be a
join-homomorphism from `(℘(A), ⊆)` on causally closed accepted sets: for any
two accepted sets `A₁`, `A₂` each closed under cited predecessors,
`σ(A₁ ∪ A₂) = σ(A₁) ⊔ σ(A₂)`. Causal closure is the condition under which a
domain selector, which reads the opener's `initial` field, is a function of
the act alone; every accepted set a replica holds is causally closed by
admission ([[SPEC-019-state-rules]] R.1), so the restriction excludes no real
history. The sixteen shipped heads SHALL be abbreviations
of terms, and the term's displayed value SHALL equal the shipped fold's value
on every conformance vector.
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
as `reached tᵢ` for the unique `tᵢ ≤ σ`, or `pending`. A reached observation
SHALL never be retracted as the accepted set grows, and SHALL be identical on
every replica whose accepted set contains the acts that reached it, whatever the
delivery order.
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
Trace: [[SPEC-038-lvar-state-kernel#TEST-3804]].

## REQ-3805: Snapshot discipline for projections

A rendered field value that is neither a reached threshold nor frozen SHALL be
marked as a snapshot in the state schema, and the host documentation SHALL
state that an external effect fired on a snapshot has no finality guarantee
from this kernel. The existing fold outputs remain available unchanged; this
requirement adds the marking, not a restriction.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3805]].

## REQ-3806: Quasi-determinism

The Lean model SHALL prove: for two replicas satisfying the premises of
[[SPEC-037-state-kernel-sec#CON-3700]] and any field, either both eventually
observe the same threshold results and the same frozen value, or at least one
observes ⊤ whose evidence names acts in conflict. Conditional strong eventual
consistency ([[SPEC-037-state-kernel-sec#REQ-3702]]) SHALL be recovered as the
case in which ⊤ never occurs. The proof SHALL introduce no sorry or custom axiom.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3806]].

## REQ-3807: No change to existing wire forms or addresses

Every existing dialect SHALL parse, install and fold identically. Every
conformance vector in `test-vectors/state/` SHALL produce byte-identical
addresses and verdicts, and identical rendered state except for the additive
`frozen`, `fault` and threshold members this specification introduces, which
SHALL appear only when a dialect declares the corresponding form.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3807]].

## REQ-3808: Closure heads

`progress` and `bounded-counter` SHALL be modelled as monotone, non-morphism
primitives whose value is a least fixed point over cited acts, with their
existing proofs ([[SPEC-034-owned-progress-closure]], [[SPEC-019-state-rules#CON-1908]])
retained. They SHALL participate in threshold reads (`progress` reaching its
bound; a resource `fault`) and in freeze. Whether they share one closure
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
field other than an `initial` field through a domain: a put that depended on a
revisable field would make admission or the fold read its own output, which is
the feedback the stratification result of [[SPEC-019-state-rules#REQ-1914]]
forbids. Cross-field conditions on revisable values are therefore expressible
only as derived snapshots or as thresholds, never as selectors.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3800]], [[SPEC-038-lvar-state-kernel#TEST-3801]].

## NFR-3800: Cost

Evaluating any term over an accepted set of `n` acts SHALL take time linear in
`n` times the term's size, with no per-act work exceeding the existing R2
bounds; the pairwise-incompatibility check of a threshold set of `k` elements
SHALL take `O(k²)` lattice comparisons at installation and none at fold time.
Trace: [[SPEC-038-lvar-state-kernel#TEST-3803]].

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
```

Pre-conditions: acts are unique by address; the clause installed under R7.
Post-conditions: for every factored head, (i) `L` is a join-homomorphism from
accepted sets, (ii) the displayed value equals [[SPEC-019-state-rules]] R.2's
fold. Error model: none; the evaluator is total.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3800]], [[SPEC-038-lvar-state-kernel#REQ-3801]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3800]].

## CON-3801: Threshold clause

Wire grammar, an entry of the `state` clause recognised by the existing
S-expression recogniser and checked at install, no new lexical forms:

```text
entry     := … | "(" "threshold" name field element+ ")"
element   := scalar | "(" "count" integer ")" | "(" "member" scalar ")"
           | "(" "sum" integer ")" | "(" "progress" integer ")" | "fault"
```

`element` forms are typed against the field's carrier: `count n` against
`addrs`, `member x` against `vals` or `entries`, `sum n` against `amounts`,
`progress n` against the progress chain, `fault` against any carrier's ⊤, and a
bare scalar against `bool` (`#t`). Install rejects any element not admitted by
the carrier and any pair of elements that are compatible. Rendering:
`{"status":"reached","element":…}` or `{"status":"pending"}` as a field named
`name` in clause order.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3802]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3801]], [[SPEC-038-lvar-state-kernel#TEST-3803]].

## CON-3802: Freeze clause

```text
entry  := … | "(" "freeze" field verb [policy] ")"
policy := "supersede" | "fault"                      ; default supersede
```

Pre-conditions: `verb` is a performative with a `:from` role; `field` is a
declared state field. Receipt admits the freezing act like any other; the fold
computes the field over acts not causally after the freeze (an act is after the
freeze when the freezing act is in its accepted causal history), applies the
policy to the rest, and renders `{"frozen": "<address>", …}` alongside the
value. Error model: install rejects an undeclared field or verb.
Implements: [[SPEC-038-lvar-state-kernel#REQ-3803]].
Verified by: [[SPEC-038-lvar-state-kernel#TEST-3802]].

## ADR-3800: LVars as the model of the state kernel

Decision: adopt the LVar store, with put, threshold read and freeze, as the
semantics the kernel aspires to, and quasi-determinism as its theorem.
Alternatives: keep the fold as an unclassified set function (status quo; leaves
finality to hosts and gives no exactly-once property); adopt CRDT state alone
(gives the lattice but not the read discipline); adopt full Bloom^L with
user-defined lattices (gives expressiveness at the cost of unproved merges,
rejected by [[SPEC-038-lvar-state-kernel#ADR-3801]]). Consequence: the
non-monotone projections stop being an exception; they are snapshots, readable
after a freeze or through a threshold, and the chain's last step is located
exactly.

## ADR-3801: A closed algebra, no user merge functions

Decision: dialects compose terms from the primitives of
[[SPEC-038-lvar-state-kernel#CON-3800]]; they cannot define carriers or join
functions. Rationale: R1 to R3 exist to keep installed dialects from adding
computational power, and a user-supplied merge is code. Consequence: a new
primitive is a new proof, as today, but a new rule head is a term and needs no
proof.

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

## TEST-3800: Factorisation and morphism law

For every conformance vector in `test-vectors/state/` and every field whose head
factors, (a) the term's displayed value equals the shipped fold's value on the
accepted set, in forward, reversed and duplicated delivery; (b) for the partition
of the accepted set into even and odd positions, and into first and second
halves, `L(A₁ ∪ A₂) = L(A₁) ⊔ L(A₂)`; (c) the two closure heads report `None`
from `factor`. Validates REQ-3800, REQ-3801, REQ-3808.

## TEST-3801: Threshold determinism

Property test: for a dialect declaring thresholds over `count`, `set-union`,
`counter` increments and `progress`, any permutation and duplication of a
delivery reaches the same element, the element is reached at most once, and a
reached element is never retracted on any superset. Validates REQ-3802.

## TEST-3802: Freeze

A `close` verb freezes a `values` field. After `close`, the rendered field
carries `frozen`; a later write that cites `close` is excluded under
`supersede` and faults the field under `fault`; a write concurrent with `close`
is treated per policy; reads before `close` are unmarked snapshots.
Validates REQ-3803.

## TEST-3803: Install rejects compatible thresholds

Installing `(threshold t coins (sum 10) (sum 20))` is rejected because the
two elements are comparable; `(threshold t coins (sum 10) fault)` is accepted;
`(threshold t flag #t #t)` is rejected as duplicate; a `count` element against
a `vals` carrier is rejected as mistyped; the check runs in `O(k²)` comparisons.
Validates REQ-3802, NFR-3800.

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
reaches ⊤ on one replica, every replica with the conflicting acts accepted
reaches ⊤ with the same evidence. Validates REQ-3806.

## TEST-3807: Vectors unchanged

Every vector's addresses, verdicts and rendered state are byte-identical to
`main` before this specification, except for members the vector's dialect
explicitly declares. Validates REQ-3807.

## Purity Boundary Map

### Pure Core (no I/O, no shared state, deterministic)
- `cbcl_core::lattice`: terms, carriers, join, evaluation, display.
- `cbcl_core::state::fold`: unchanged; the existing evaluator.
- Install checks for threshold incompatibility and freeze roles.

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
