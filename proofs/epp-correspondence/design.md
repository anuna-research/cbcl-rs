# Design: Formal Model for the EPP Correspondence Theorem

**Date:** 2026-06-25
**Paper:** *Choreography without a Choreographer: Replicated Endpoint Projection*
**Goal:** Turn Conjecture 1 (the endpoint-projection correspondence) into a proved
theorem for a results paper. This document fixes the formal model the theorem is
stated over, the theorem statement, and the proof strategy, before any prose or Lean
is written.

## Milestone scope

**Paper-level rigorous proof first; Lean mechanization is the following milestone.**
Rationale: the proof will shake out the exact R6 / compatibility side-conditions, and
mechanizing a wrong model is wasted effort. The model is designed to be
mechanization-friendly (configurations are sets; validity/completion are predicates;
gluing is union) so the Lean step is a translation, not a redesign.

## Foundational decisions (settled in brainstorming)

1. **Semantic domain = causal configuration (DAG-native).** A run is a down-closed set
   of messages in the content-addressed causal DAG, not an interleaved trace. Gluing is
   union-by-hash; the valid-sticky lattice is already monotone over a growing set; best
   fit for CBCL's store and the existing R5 development.
2. **Validity is two-level: safety + completion.** Safety is the monotone per-message
   core (the verifier reaching non-`Violation`); completion is a separate terminal
   predicate. Mirrors the paper's existing safety (`Violation`) vs. liveness
   (`Unknown` / vacant role) split.
3. **Bundle-omission is contained by a compatibility precondition + sealing; R6 is
   unchanged.** The completeness direction is stated over *compatible* families;
   sealing turns an omitted fan-in member into a `Violation`/`Unknown`. We do **not**
   add an observability clause to R6.
4. **Paper proof first, Lean next** (see Milestone scope).

## Revision 2026-06-26 (post Task-5 review)

A rigorous review of the load-bearing reconciliation lemma found its proof did not
close: it conflated the *protocol-level* predecessor splice with the *run-level* (hash)
splice and never established that they agree, and the original `Coverage` clause was
inconsistent with bystander erasure. Four fixes, applied throughout the model below
(**R6 unchanged**):

1. **Conformance hypothesis.** The reconciliation lemma (and soundness) assume a
   *P-safe* configuration. P-safety already entails per-message role conformance
   (role-local verification, `def:rolelocal`), and the correspondence theorem only ever
   applies the lemma to P-safe `C` / families — so this tightens a hypothesis, no new
   machinery. It is what licenses the key step *a message is r-relevant iff its
   performative is r-relevant* (role annotations live on performatives; conforming
   messages inherit them).
2. **Projection rewrites predecessors.** `project(C, r)` replaces each retained
   message's raw `pred` with its *r-observable spliced predecessor set* `pred_r` (§4).
   Local validity and `Coverage` are stated over `pred_r`, making them consistent with
   bystander erasure (raw `pred` may point at erased bystanders, which a local run does
   not hold).
3. **Explicit splice-commutation lemma.** A new lemma (`lem:splice`, by induction on
   bystander-chain length) establishes the commuting square: following raw `pred` edges
   through `C` / `glue(F)` and skipping bystanders yields exactly the messages named by
   the spliced protocol edges of `project(P, r)`. `lem:reconcile` cites it instead of
   asserting coincidence.
4. **Fan-in as sets.** Predecessors are sets; the correspondence is set-equality.
   R6-projectability ensures the fan-in members `r` depends on are r-observable (hence
   retained), so the local spliced fan-in equals the global one restricted to
   r-observable members; members `r` never observes are simply absent from
   `project(P, r)`.

## The model

### 1. Substrate

A **message** `m` has: content hash `h(m)`, performative type `τ(m)`, sender role
`from(m)`, recipient role set `to(m)`, and predecessor-hash set `pred(m)`. All
references are thread-scoped (ADR-008): every hash in `pred(m)` resolves within the
same thread. A **protocol** `P` (a role-annotated causal protocol satisfying R6) gives,
per performative type, its allowed predecessor clauses (`(any …)` / `(all …)`) and its
sender/recipient role annotations.

*Open modelling points to confirm during write-up:* multi-recipient messages
(`to(m)` a set) and multi-occupant roles (pooled `(any role[*])` / indexed
`(all role[*])`) from the cardinality discussion — the definitions below are written to
accommodate sets but the proofs should be checked against the multi-occupant case.

### 2. Global execution = configuration

A **configuration** `C` is a finite set of messages. `C` is **closed** iff causally
down-closed: for every `m ∈ C`, every hash in `pred(m)` resolves to some `m' ∈ C`.
Partial runs need not be closed — a dangling predecessor yields `Unknown`, never
`Violation`. Global executions of interest are *closed* configurations (complete causal
histories).

### 3. Global validity (two-level)

- **Safety.** `C` is *P-safe* iff no `m ∈ C` has verdict `Violation` under `P`
  (`Unknown` is tolerated). Monotone in the valid-sticky order: a subset of a P-safe
  configuration is P-safe.
- **Completion.** A closed `C` is *P-complete* iff it is P-safe and every obligation is
  discharged: every sealed `(all …)`-fan-in has all members present and `Valid`, and no
  required step for the taken branches is missing. A terminal snapshot; not monotone, by
  design.

### 4. Local execution = projection of a configuration

A message `m` is **r-relevant** iff `from(m) = r` or `r ∈ to(m)`; otherwise it is a
**bystander** for `r`. `project(C, r)` retains the r-relevant messages of `C`, erases
bystanders, and **rewrites each retained message's predecessors**: define the
*r-observable spliced predecessor set*

> `pred_r(m)` = the set of nearest r-relevant ancestors of `m` under `pred` — i.e.,
> follow `pred` edges from `m`, skipping bystanders transitively, and collect the first
> r-relevant message on each path.

The retained message in `project(C, r)` carries `pred_r(m)` in place of its raw
`pred(m)`. (`project(P, r)` performs the matching rewrite on protocol edges, per the
paper's Definition of Projection.) Raw `pred(m)` may point at bystanders that the local
run does not hold; `pred_r` is exactly the part `r` can observe, so local validity and
`Coverage` (§5) are stated over `pred_r`, not raw `pred`.

- `L` is *locally P-safe for `r`* iff no message in `L` is `Violation` under
  `project(P, r)` (over `pred_r`) with `r`'s store `= L`.
- `L` is *locally complete for `r`* analogously (terminal w.r.t. `project(P, r)`).

**Bridge:** `thm:equiv` (projectability ≡ local verifiability) — under R6, `r` never
gets a spurious `Unknown` for a predecessor it cannot observe.

### 5. Gluing and compatibility

A **family** `F = {L_r}_{r ∈ roles}` has one local run per role. `F` is **compatible**
iff:

- *(Agreement)* any message appearing in two runs (identified by `h`) is identical —
  immediate from content addressing.
- *(Coverage)* every message `m ∈ L_r` appears in `L_{r'}` for each of its other
  endpoints `r' ∈ {from(m)} ∪ to(m)`, and every member of `m`'s *r-observable spliced
  predecessor set* `pred_r(m)` is present in `L_r`. (Stated over `pred_r`, not raw
  `pred`: a local run holds only r-relevant messages, so requiring raw bystander
  predecessors in `L_r` would contradict erasure. Bystander predecessors are recovered
  globally by gluing the runs of the roles that *do* observe them.)

`glue(F) = ⋃_r L_r` (deduplicated by hash). Agreement ⇒ `glue` is well-defined;
Coverage across all roles ⇒ every raw predecessor reappears in some `L_{r'}`, hence
`glue` is closed.

### 6. Theorem (replaces Conjecture 1)

**EPP correspondence.** Let `P` satisfy R6. Then:

1. **Soundness (global → local).** If `C` is a P-safe [resp. P-complete] closed
   configuration, then for every role `r`, `project(C, r)` is locally P-safe [resp.
   locally complete] for `r` against `project(P, r)`.
2. **Completeness (local → global).** If `F = {L_r}` is a *compatible* family with each
   `L_r` locally P-safe [resp. locally complete], then `glue(F)` is a P-safe [resp.
   P-complete] closed configuration.
3. **Exactness (round-trip).** On valid objects, `project` and `glue` are mutually
   inverse: `glue({project(C, r)}_r) = C` for P-safe closed `C`, and
   `project(glue(F), r) = L_r` for compatible families `F`. Hence valid global runs and
   compatible valid local families are in bijection — the endpoints realise *exactly*
   `P`.

### 7. Proof strategy

The chain is: **`lem:splice` (commuting square) → `lem:reconcile` → soundness /
completeness / exactness.**

- **`lem:splice` (bystander-splice commutation, the new engine).** For a *P-safe*
  configuration `C` and role `r`: for each r-relevant `m`, the r-observable spliced
  predecessor set `pred_r(m)` computed over `C`'s raw `pred` edges equals (as a set, by
  hash) the predecessor set named by `project(P, r)` for `m`. *Proof by induction on
  bystander-chain length.* Base: a raw predecessor `m'` of `m` that is r-relevant —
  P-safety gives that `m'` conforms to `P`, so `τ(m')` is a legal P-predecessor of
  `τ(m)` and the edge survives projection. Step: a raw predecessor `b` that is a
  bystander — P-safety makes `b` conform, so `b` is a bystander *for `r`* exactly when
  its performative is (role annotations live on performatives); protocol-projection
  erases that performative and splices through it, and by IH `b`'s `pred_r` matches
  `project(P, r)`'s spliced edges, so composing the splice at `m` gives the result. This
  is precisely the step the old proof asserted; the two transitive closures
  (protocol-edge vs. hash-edge) commute *because conformance ties message-relevance to
  performative-relevance*.

- **`lem:reconcile` (now a corollary of `lem:splice`).** (i) For P-safe closed `C` and
  `m ∈ project(C, r)`, `pred_r(m)` resolves within `project(C, r)` (iterated closure
  down bystander chains) and matches `project(P, r)` (`lem:splice`). (ii) For a
  compatible family with each `L_r` locally P-safe, `pred_r(m)` is present in `L_r`
  (Coverage) and, by Agreement, equals the global witnesses in `glue(F)`.

- **Soundness:** `lem:reconcile`(i) + `thm:equiv`; role conformance is a per-message
  predicate unaffected by projection; sealing carries through. 
- **Completeness:**
  - *Safety* — each `m ∈ glue(F)` lies in some `L_r`; `pred_r(m)` present (Coverage) and
    conformant (local safety), reconciled to the global predecessors by
    `lem:reconcile`(ii); `glue` closed by `lem:glue-closed`.
  - *Completion* — sealing makes any omitted member of a sealed fan-in a local
    `Violation`/`Unknown`, contradicting local completeness; bundle-omission neutralised.
- **Fan-in (cardinality).** A named predecessor may be a *set* (`(all …)`/`(any …)`,
  pooled/indexed roles). R6-projectability ensures the members `r` depends on are
  r-observable, hence retained; so the local spliced fan-in equals the global one
  restricted to r-observable members, and `lem:splice`/`lem:reconcile` are stated and
  proved for predecessor **sets**, not single predecessors.
- **Exactness:** set algebra on hashes (filter+splice vs. union), mutually inverse given
  compatibility and closure.

### 8. Risk and honest caveat

Bundle-omission (REQ-311: a causal-closure bundle cannot prove no sibling branch was
omitted) is contained by **compatibility (Coverage) + sealing**, so **R6 is unchanged**.
The paper will state plainly that the completeness direction is conditioned on
*compatibility*, a meta-level gluing precondition that a single endpoint cannot verify
from its own view (it verifies only its local run). This is a true, clearly-stated limit
— not a hidden assumption.

## What changes in the paper

- Add a **Formal Model** section (substrate, configuration, two-level validity,
  projection-on-runs, compatibility, gluing) expanding the current terse setup.
- Replace **Conjecture 1** with the **EPP correspondence theorem** and its proof: full
  for soundness; completeness with the compatibility precondition; exactness as the
  round-trip.
- Keep the Lean mechanization framed as the next milestone (the current honesty footnote
  about axioms / post-parse DCFL predicates stays accurate).

## Open obligations carried into write-up / mechanization

- ~~Confirm the completion predicate against multi-occupant (pooled/indexed) roles and
  multi-recipient messages.~~ Resolved by the §7 fan-in argument (sets +
  R6-projectability) and `pred_r` over recipient sets.
- ~~Confirm the spliced-vs-global predecessor reconciliation lemma is stated precisely.~~
  Resolved: replaced by `lem:splice` (induction on bystander-chain length) with
  `lem:reconcile` as its corollary (Revision 2026-06-26).
- Verify, during write-up, that `pred_r` (nearest r-relevant ancestors) is well-defined
  on cyclic-free DAGs and that the iterated-closure step in `lem:reconcile`(i) terminates
  (it does: bystander chains are finite in a finite configuration) — make the induction
  measure explicit in the proof.
- Decide whether `compatibility` should eventually be made endpoint-checkable (future
  work; not required for this milestone).
