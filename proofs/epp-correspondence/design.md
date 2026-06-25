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

`project(C, r)` is the sub-run of messages `m ∈ C` with `from(m) = r` or `r ∈ to(m)`,
with bystander messages erased and causal edges spliced (transitive closure through
erased nodes) — the paper's Definition of Projection, lifted from protocols to runs.

- `L` is *locally P-safe for `r`* iff no message in `L` is `Violation` under
  `project(P, r)` with `r`'s store `= L`.
- `L` is *locally complete for `r`* analogously (terminal w.r.t. `project(P, r)`).

**Bridge:** `thm:equiv` (projectability ≡ local verifiability) — under R6, `r` never
gets a spurious `Unknown` for a predecessor it cannot observe.

### 5. Gluing and compatibility

A **family** `F = {L_r}_{r ∈ roles}` has one local run per role. `F` is **compatible**
iff:

- *(Agreement)* any message appearing in two runs (identified by `h`) is identical —
  immediate from content addressing.
- *(Coverage)* every sent message appears in its recipient's run, and every referenced
  predecessor hash is present in the relevant role's run.

`glue(F) = ⋃_r L_r` (deduplicated by hash). Agreement ⇒ `glue` is well-defined;
Coverage ⇒ `glue` is closed.

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

- **Soundness:** `thm:equiv` + erasure-with-splicing preserves r-observable
  predecessors; sealing carries through projection. Largely in hand from the existing
  development.
- **Completeness (the technical content):**
  - *Safety* — each `m ∈ glue(F)` lies in some `L_r`; its P-predecessors are present
    (Coverage) and conformant (local safety + Agreement). The spliced (local) vs.
    global predecessor chain is reconciled by closure of `glue`.
  - *Completion* — sealing makes any omitted member of a sealed fan-in a local
    `Violation`/`Unknown`, contradicting local completeness; this is where
    bundle-omission is neutralised.
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

- Confirm the completion predicate against multi-occupant (pooled/indexed) roles and
  multi-recipient messages.
- Confirm the spliced-vs-global predecessor reconciliation lemma is stated precisely
  (the load-bearing step of the completeness/safety proof).
- Decide whether `compatibility` should eventually be made endpoint-checkable (future
  work; not required for this milestone).
