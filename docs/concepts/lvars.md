---
title: LVars
mode: explanation
---

# LVars

Lattice variables, the model [[SPEC-038-lvar-state-kernel]] takes for the state
kernel. Sources verified on 7 November 2026 through Crossref and the authors'
texts; section numbers refer to those texts.

## The model

**LVars** (Kuper and Newton, FHPC 2013, DOI 10.1145/2502323.2502326). A
variable holds an element of a lattice with a bottom and a top. `put` joins a
value in. `get` is a blocking *threshold read*: it takes a threshold set `Q`, a
non-empty subset of the lattice that is *pairwise incompatible*, meaning the
least upper bound of any two distinct elements of `Q` is ⊤; when the variable's
state is at or above some `d′ ∈ Q`, `get` returns `{d′}`, and that `d′` is
unique because two reached elements would force the state to ⊤. Taking a
variable to ⊤ is an error. This is the whole source of determinism: the only
observation is "which threshold element has been reached", and write order
cannot change the answer.

**LVish** (Kuper, Turon, Krishnaswami and Newton, POPL 2014, DOI
10.1145/2535838.2535842) adds two operations. *Freeze* makes a variable exact,
after which it can be read directly; a write that would move a frozen variable
is an error, and ⊤ is the error state that conflicting writes produce. *Handlers*
attach a callback that runs whenever the variable changes. The theorem is
quasi-determinism: in a language whose communication goes only through these
variables, every run either produces the same answer or raises an error. The
`freeze-after` pattern, freeze once a handler pool has quiesced, is how the
authors make freezing usable.

## Distributed relatives

**Lasp** (Meiklejohn and Van Roy, PPDP 2015, DOI 10.1145/2790449.2790525) is a
dataflow language over replicated state-based CRDTs in Erlang. Its read is a
*monotonic read*, `read(x, v)`: it waits until the replica's state is at or above
a trigger `v` and then returns that state (Definition 3.1). This is not a
threshold read. The returned value is whatever state dominates the trigger at
the time, so two replicas can return different values from the same trigger;
the guarantee is inflation, not a unique answer. Lasp's related work, §7.5,
says why it departed from LVars: a threshold read "makes two assumptions: a
priori knowledge of the internal state of a CRDT to properly threshold on the
value, and that the queryable value of a CRDT is monotone", and for CRDTs such
as observed-remove sets neither holds. Lasp cites LVars as its single-machine
ancestor. A 2025 retrospective by the same authors, "Distributed,
Coordination-Free Programming: 10 Years of Progress Since Lasp" (PPDP 2025, DOI
10.1145/3756907.3756910), surveys the line.

**Hydro, previously Hydroflow** (Berkeley, 2021 onward). A Rust dataflow
runtime whose `lattices` crate (docs.rs, version 0.7) provides `Merge`,
`LatticeOrd`, `IsBot` and `IsTop` traits, compound lattices (pairs, maps,
unions, max and min chains, `WithBot`, `WithTop`), and `LatticeBimorphism`,
"semilattice bimorphism: lattice merge must distribute over this binary
function, in both arguments". The crate's own text motivates it by the CALM
theorem. "Keep CALM and CRDT On" (Laddad, Power, Milano, Cheung, Crooks and
Hellerstein, VLDB 2022, DOI 10.14778/3574245.3574268) extends CRDTs "with a
query model that reasons about which queries are safe without coordination by
applying monotonicity results from the CALM Theorem", which is the same move as
LVars' threshold read made over CRDT queries. "Flo" (Laddad, Cheung, Hellerstein
and Milano, POPL 2025, DOI 10.1145/3704845; arXiv 2411.08274) gives the semantic
foundation.

Hydro has no freeze. Checked on 7 November 2026 across the `lattices` crate
documentation, the DFIR operator reference and the Flo text: there is no
operation that makes a lattice variable exact and rejects later writes. The
nearest things are three. `IsTop` marks a value that "cannot change any
further", a terminal lattice element rather than an operation, and `WithTop`
adds one to any lattice. `MapUnionWithTombstones` is observed removal, the
W and R pattern. And Flo makes finality a *type*: it "distinguish[es] bounded
streams, which allow operators to block on termination, from unbounded ones",
and places the stream-processing progress markers, punctuations, watermarks,
heartbeats and frontiers, under "families of collection types that admit
reasoning about fixedness". So in the Hydro line fixedness is declared
statically by the program; in LVish it is a dynamic operation; in CBCL it is a
dynamic, signed, role-permitted act that other acts can cite. That difference
is what makes a late write attributable here and merely late elsewhere.

**Datafun** (Arntzenius and Krishnaswami, ICFP 2016, DOI
10.1145/2951913.2951948) is a functional Datalog whose "key feature is to track
monotonicity with types": it has a type of monotone functions and distinguishes
discrete from monotone variables. This is the mechanism for deciding, from the
shape of a term, whether an observation is stable, which
[[SPEC-038-lvar-state-kernel#REQ-3809]] relies on.

**BloomL** (Conway, Marczak, Alvaro, Hellerstein and Maier, SoCC 2012, DOI
10.1145/2391229.2391230): lattice-valued Datalog with morphism tracking and
explicit barriers at non-monotone points.

## What the CBCL kernel takes, and what it answers

The kernel takes LVish whole: put as the join of an accepted act's contribution,
threshold reads with pairwise-incompatible sets, freeze, handlers as the
execution layer's subscriptions, ⊤ as conflict, and quasi-determinism as the
theorem to prove.

It answers Lasp's two objections by construction rather than by weakening the
read. The carriers are a closed, known algebra ([[SPEC-038-lvar-state-kernel#CON-3800]]),
so the internal state is known a priori; and thresholds are typed against the
*carrier*, never against the displayed value ([[SPEC-038-lvar-state-kernel#CON-3801]]),
so a threshold over an observed-remove set is stated on the grow-only halves,
"this address was added", "this address was removed", which are monotone, and
never on membership, which is not. Lasp's monotonic read is, in the kernel's
vocabulary, a snapshot taken after a threshold: readable, but without the
exactly-once property ([[SPEC-038-lvar-state-kernel#REQ-3805]]).

What none of these systems has, and the kernel adds underneath: puts that are
signed, content-addressed and admitted against a cast and a causal protocol
([[protocol-model]]); a freeze that is an attributable act by a role; and a ⊤
that carries the addresses in conflict as evidence.
