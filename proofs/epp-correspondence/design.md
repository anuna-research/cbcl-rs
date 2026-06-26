# Design: Formal Model for the EPP Correspondence Theorem

**Date:** 2026-06-25 (revised 2026-06-26, **v2**)
**Paper:** *Choreography without a Choreographer: Replicated Endpoint Projection*
**Goal:** Turn Conjecture 1 (the endpoint-projection correspondence) into a proved
theorem for a results paper. This document fixes the formal model the theorem is stated
over, the theorem statement, and the proof strategy, before any prose or Lean is written.

## Milestone scope

**Paper-level rigorous proof first; Lean mechanization is the following milestone.** The
model is designed to be mechanization-friendly (configurations are sets; validity is a
predicate; gluing is union) so the Lean step is a translation, not a redesign.

## Foundational decisions (settled in brainstorming)

1. **Semantic domain = causal configuration (DAG-native).** A run is a down-closed set of
   messages in the content-addressed causal DAG; gluing is union-by-hash.
2. **Validity is two-level: safety + completion.** Safety is the monotone per-message core
   (verifier reaching non-`Violation`); completion is a separate terminal predicate.
3. **Bundle-omission contained by compatibility + sealing.** (R6 gains a single
   *causal-locality* clause in v3 — see revision history — the only change to R6; nothing
   is weakened.)
4. **Paper proof first, Lean next.**

## Revision history (the crux took two iterations — recorded for honesty)

- **Original.** A load-bearing "reconciliation lemma" whose proof was a *gap*: it
  conflated the protocol-edge predecessor splice with the run-level (hash-edge) splice and
  never showed they agree.
- **v1 attempt — failed.** Introduced `pred_r` (projection *rewrites* each retained
  message's predecessors to its nearest r-observable ancestors). Rigorous review found this
  *worse*: rewriting a message's `pred` field per role breaks **Agreement** (the same hash
  carries different per-role predecessor sets) and raw-`pred` **glue-closure**, and still
  glossed `(any)` fan-in.
- **v2 — this version.** Investigation of `cbcl-rs` settled the key fact: `:caused-by` is
  **sender-chosen** — a content-hash pointer to a concrete predecessor *instance*, checked
  only for legal predecessor *type*, one direct edge; there is **no** transitive /
  observability-aware mechanism, and multiparty is **undefined** (R5 is binary-only). A
  sender can therefore only reference messages **it observes**, and **R6 projectability**
  guarantees those references are observable to the message's *recipients* too. Hence, in a
  P-safe run of a projectable protocol, **there are no bystander-mediated dependencies** —
  every causal edge is directly observable to all its dependents. The reconciliation
  problem *dissolves*: projection keeps raw `caused-by`, and a **Local-resolvability**
  lemma (from projectability + conformance) replaces the entire splicing apparatus. `pred_r`
  is dropped. The paper notes that CBCL's multiparty causal semantics are undefined today
  and that our projection *defines* them via this observable-reference obligation (which R6
  already enforces at the type level).
- **v3 — causal locality (current).** Rigorous review showed v2's Local-resolvability
  lemma was *still* false: `def:proj`'s bystander-splice permits a message whose
  `caused-by` points at a performative that is a **bystander** for one of its endpoints —
  which projectability (defined *via* splicing) tolerates. The fix is a genuine
  well-formedness condition, **causal locality**: every endpoint of a performative is also
  an endpoint of each of its `caused-by` predecessor types. Added as an R6 clause it makes
  the bystander-splice vacuous, makes Local resolvability provable, and matches the code
  fact that `caused-by` is one direct sender-chosen edge. **This is arguably a
  contribution: multiparty CBCL projection requires causal locality.** Also added in v3:
  the `closed` hypothesis on Local resolvability; a `(Seal)` cast-agreement clause in
  compatibility; and a completion-reconciliation lemma (sealing/fan-in are *global*, so the
  safety lemmas do not cover the completion direction).

## The model

### 1. Substrate

A **message** `m` carries a content hash `h(m)`, performative type `τ(m)`, sender role
`from(m)`, recipient role set `to(m)`, and predecessor-hash set `pred(m)` (its sender-chosen
`:caused-by`). All references are thread-scoped (ADR-008). A protocol `P` (role-annotated,
satisfying R6) fixes, per performative, its predecessor clauses (`(any …)`/`(all …)`) and
its sender/recipient role annotations.

### 2. Global execution = configuration

A **configuration** `C` is a finite set of messages; **closed** iff causally down-closed
over raw `pred`. A dangling predecessor yields `Unknown`, never `Violation`. Global
executions of interest are *closed* configurations.

### 3. Global validity (two-level)

- **Safety.** `C` is *P-safe* iff no `m ∈ C` has verdict `Violation` under `P` (`Unknown`
  tolerated). Subset-closed.
- **Completion.** A closed `C` is *P-complete* iff P-safe and every obligation is
  discharged: each taken branch's required performatives present; every sealed
  `(all role[*])` fan-in has all members present and `Valid`; every pooled `(any role[*])`
  obligation has ≥1 occupant.
- **Conformance via safety (tightening of `def:rolelocal`).** Role-local verification
  checks each message's `from/to` against the sender/recipient roles `P` annotates for its
  performative, failing to `Violation` on mismatch. So a **P-safe configuration is
  role-conformant**: every message's roles match its performative's annotations. (This is
  exactly the role-conformance check present in `cbcl-rs`; the recap states it explicitly so
  the proof can use it.)

### 4. Local execution = projection

A message `m` is **r-relevant** iff `from(m) = r` or `r ∈ to(m)`. `project(C, r)` is the set
of r-relevant messages of `C`, **retaining their raw `caused-by`** (no rewriting).
`project(P, r)` is role `r`'s local protocol (the paper's Definition of Projection).

- `L` is *locally P-safe for `r`* iff no `m ∈ L` is `Violation` under `project(P, r)` with
  store `L`.
- `L` is *locally complete for `r`* analogously.

### 5. Gluing and compatibility

A **family** `F = {L_r}` has one local run per role. `F` is **compatible** iff:

- *(Agreement)* equal-hash messages across runs are identical (immediate from content
  addressing — and now unproblematic, since projection does not alter messages).
- *(Coverage)* for every `m ∈ L_r`: **(a)** `m ∈ L_{r'}` for each endpoint
  `r' ∈ {from(m)} ∪ to(m)`; **(b)** every `caused-by` predecessor of `m` is itself in
  `L_r` — i.e. each local run is *causally closed*. (This is exactly the property
  `project(C, r)` has by Local resolvability, §7, so requiring it of a family asks no more
  than that each run be a genuine projection.)

`glue(F) = ⋃_r L_r` (dedup by hash). Agreement ⇒ well-defined; Coverage(b) ⇒ closed (each
`m ∈ glue(F)` lies in some `L_r` with its predecessors in `L_r ⊆ glue(F)`).

### 6. Theorem (replaces Conjecture 1)

**EPP correspondence.** Let `P` satisfy R6. Then:

1. **Soundness.** If `C` is P-safe [resp. P-complete] closed, then each `project(C, r)` is
   locally P-safe [resp. locally complete] for `r`.
2. **Completeness.** If `F` is *compatible* with each `L_r` locally P-safe [resp. locally
   complete], then `glue(F)` is P-safe [resp. P-complete] closed.
3. **Exactness.** `project` and `glue` are mutually inverse on valid objects, so valid
   global runs and compatible valid local families are in bijection — the endpoints realise
   *exactly* `P`.

### 7. Proof strategy (v2)

- **Local resolvability (the engine).** *In a P-safe **closed** configuration of an R6
  protocol, for every message `m` and every endpoint `r` of `m`, all of `m`'s `caused-by`
  predecessors are r-relevant, hence lie in `project(C, r)`.* Proof: `C` closed ⇒ `m`'s
  verdict is decided, and P-safe ⇒ `m` is `Valid`, so each named predecessor `b` has a legal
  type `T`; **causal locality** (R6) ⇒ every endpoint of `τ(m)` is an endpoint of `T`, so
  `r` is an endpoint role of `T`; conformance (P-safety, §3) ⇒ `r ∈ endpoints(b)` ⇒ `b` is
  r-relevant. **No induction, no bystander chains** — causal locality rules
  bystander-mediated dependencies out (`def:proj`'s splice is vacuous).
- **Reconciliation (verdict-based, now trivial).** For r-relevant `m`, local verification
  over `project(P, r)` and `L = project(C, r)` reads the *same* `caused-by` edges as global
  verification and (Local resolvability) resolves them in `L`, so returns the *same* verdict.
  `(any)`/`(all)` fan-in is handled identically in both views by the verifier checking the
  actual edge(s) against the clause — **no set-equality obligation**, so no fan-in gap.
- **Soundness:** each retained `m ∈ project(C, r)` has the same (non-`Violation`) verdict
  locally as globally (reconciliation); completion carries via sealing preserved under
  projection.
- **Completeness:** `glue(F)` closed (`lem:glue-closed`, Coverage(b)); each `m ∈ glue(F)`
  lies in some `L_r` where it is non-`Violation`, its predecessors present (Coverage) and
  verdict matched (reconciliation) ⇒ `glue(F)` P-safe. Completion by the sealing
  contrapositive (an omitted member ⇒ a local undischarged obligation, contradiction).
- **Exactness:** set algebra — every message has a sender (so ≥1 endpoint), Coverage gives
  the round-trip.

### 8. Risk and caveat

Bundle-omission contained by compatibility (Coverage) + sealing; **R6 unchanged**. The
completeness direction is conditioned on *compatibility*, a meta-level gluing precondition a
single endpoint cannot verify alone — stated plainly. New honest framing: **CBCL's
multiparty causal semantics are undefined today; our projection defines them** by requiring
each message's `caused-by` reference predecessors observable to all its endpoints — an
obligation R6 projectability already enforces at the type level.

## What changes in the paper

- Add a **Formal Model** section (substrate, configuration, two-level validity, projection,
  compatibility, gluing) and the **Local-resolvability** lemma.
- Replace **Conjecture 1** with the **EPP correspondence theorem** + proof.
- State the observable-reference obligation as part of well-formedness, noting projection
  *defines* multiparty `caused-by`.
- Tighten the description of role-local verification to include the role-conformance →
  `Violation` check (already in `cbcl-rs`).
- Lean mechanization stays the next milestone.

## Open obligations carried into write-up / mechanization

- The `def:rolelocal` tightening (role mismatch ⇒ `Violation`) must match the `cbcl-rs`
  conformance check — confirmed present in code; state it precisely when porting.
- ~~Reconciliation / spliced-vs-global lemma~~ — **resolved**: replaced by Local
  resolvability (no splicing).
- ~~Multi-occupant / multi-recipient cardinality~~ — handled: verdict-based reconciliation
  checks the actual `(any)`/`(all)` edges identically; `to(m)` is a set throughout.
- Decide whether `compatibility` should be made endpoint-checkable (future work).
