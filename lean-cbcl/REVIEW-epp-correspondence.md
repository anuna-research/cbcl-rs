# Review: endpoint-projection proofs in `lean-cbcl`

**Date:** 2026-07-10 · **Scope:** `EPP.lean`, `EPPCompletion.lean`, `Projectability.lean`,
`Splice.lean`, `Bridge.lean`, cross-checked against `proofs/epp-correspondence/proof.tex`,
SPEC-014, and the repo README.

## Verdict

**No mathematical bugs found.** `lake build` passes, the sorry analyzer reports 0 sorries
across all 30 files, and a fresh `#print axioms` probe confirms every headline theorem
(`epp_correspondence`, `epp_correspondence_complete`, `projectability_iff_local_verifiability`,
`causal_locality_necessary`, `type_opacity_indistinguishability`, `weakest_sound_condition`,
`openings_suffice_concrete`, `temporal_bridge`) depends only on `propext`,
`Classical.choice`, `Quot.sound` (several on fewer; the two counterexample theorems on none).
The two hand-built counterexamples (`Projectability.Counterexample`, `Splice.Example`) were
checked case-by-case and are correct. The proofs prove what their formal statements say.

The findings below are **fidelity gaps between the formal statements and the surrounding
claims** (docstrings, `proof.tex`, README), plus modeling choices whose intent should be
stated more explicitly. Ordered by significance.

## Resolution log (2026-07-10, same session)

All findings were worked through after the review; `lake build` passes and
`scripts/check-axioms.sh` reports 36 theorems audited, all axioms allowlisted.

1. **Resolved (interface-level) + documented.** New `LeanCbcl/ProtocolProjection.lean`:
   `AgreesOnRole D Q r` specifies exactly what a Def-1 projected protocol must preserve
   (message fields + protocol fields at `r`-endpoint performatives);
   `local_protocol_verification_agrees` proves that any such `Q`, verified against its own
   projected store, decides every `r`-relevant verdict and agrees with the global verifier
   — i.e. Def. 3 + reconcile(i) with the projected protocol restored to the statement.
   The remaining paper-level step (the concrete splice satisfies `AgreesOnRole` under
   causal locality) is now stated explicitly in `EPP.lean`'s header, `proof.tex` §Notes,
   and the README mapping table; mechanizing it would require a concrete clause syntax.
2. **Resolved.** `epp_correspondence` and `epp_correspondence_complete` now package both
   round-trip identities (family-side `project_glue_eq` conjunct added, quantified over
   arbitrary compatible families).
3. **Resolved (documented).** `EPP.lean` header now carries the resolved-first scope note
   citing ADR-602; `proof.tex` gained a "Remark (verdict timing)" after Def. 3 stating
   both semantics and where they coincide.
4. **Resolved.** `Obligations` generalized to witness-*sets* (`oblig : Role → (Msg → Prop)
   → Prop`), so pooled `(any role[*])` obligations are genuinely disjunctive — different
   runs may discharge one via different occupants and gluing still works. The
   present-vs-present∧Valid strengthening is proved vacuous on the correspondence domain
   (`valid_of_safe_closed` in `EPP.lean`, `dischargedFor_of_present` in
   `EPPCompletion.lean`). The (Seal)-by-fiat limitation is now stated bluntly in the
   header. Redundant `hcl`/`hsafe` hypotheses of `epp_correspondence_complete` dropped
   (derived from `pComplete`).
5. **Resolved.** `type_opacity_indistinguishability` strengthened: the decider `f` now
   also receives the typed observation `heldTypes D C r` (held messages with their
   performatives), and `heldTypes D₁ C r = heldTypes D₂ C r` is a conjunct of the
   witness. The prose and the formal statement now match. README's `openings_suffice`
   entry rewritten to attribute the Merkle construction to Rust and the factoring theorem
   to Lean.
6. **Resolved (documented).** Clarifying notes added to `EPP.lean`'s header and
   `reconcile_global`'s docstring, pointing at `bridge_stability` /
   `unknown_means_not_yet_arrived` for the genuinely three-valued statements; the
   presence⇒validity fact is now the named lemma `valid_of_safe_closed`.
7. **Resolved.** `AxiomAudit.lean` extended with 22 `#print axioms` lines covering the
   EPP family (including the new `ProtocolProjection.lean` theorems); the CI script
   passes (36 theorems, allowlisted axioms only). `proof.tex` §Notes now says the axiom
   claim is CI-enforced.
8. **Resolved (documented).** `legalPred`/`clause` slack noted on `Proto`'s docstring;
   `Schedule.bounded` docstring states the misdelivery exclusion;
   `causal_locality_necessary` docstring explains why the converse is existential
   (the per-protocol converse is false over impoverished `Msg` types). The
   abstract-vs-concrete (`CBCL.Verify`) disconnect and `resolution_requires_preimage`'s
   framing hypothesis remain as-is, by design — both already documented in `Splice.lean`.

---

## 1. Protocol projection is not mechanized — local verification uses the *global* protocol

`proof.tex` Def. 1 defines `project(P, r)` (bystander performatives erased, causal edges
spliced transitively through the erasure), and Def. 3 + Lemma reconcile(i) compare
verification of a message **over `project(P,r)`** against verification **over `P`**.

The Lean model has no protocol projection at all. `localSafe`, `good`, and every
reconciliation lemma evaluate both sides against the *same* `P` (`EPP.lean:92`,
`EPP.lean:177`); only the **store** is projected (`EPP.lean:90`). The paper-level step
"under causal locality the bystander-splice is never exercised, so `project(P,r)` and `P`
agree on `r`-relevant messages" is argued in prose (R6 note, `proof.tex:84-93`) and never
formalized. `Splice.lean` §3 (`weakest_sound_condition`) is about *store*-locality of
predecessors, not about the protocol splice of Def. 1.

Consequences:
- The header claim "Mirrors `proofs/epp-correspondence/proof.tex`" (`EPP.lean:4`) overstates:
  the store-reconciliation half is mechanized; the protocol-projection half is not.
- README's mapping table (line 128) maps `projection.rs` → `EPP.lean`, but the splicing
  transformation `projection.rs` implements has no Lean counterpart theorem.

Not a soundness bug — but it is the single largest gap between what is claimed as
"mechanized" and what is. Recommend either (a) a one-paragraph disclaimer in `EPP.lean`'s
header and README ("protocol projection is identified with `P` on r-relevant messages;
this identification is paper-level"), or (b) mechanizing a minimal `projectProto` and the
agreement lemma.

## 2. `epp_correspondence` omits half of the paper's Exactness claim

`proof.tex` Thm. epp(3) claims *both* round trips: `glue(project C) = C` **and**
`project(glue F, r) = L_r`, i.e. a bijection. The packaged theorem
(`EPP.lean:267-275`) includes only the first (`glue_project_eq`). The second is proved
(`project_glue_eq`, `EPP.lean:253`) and *is* packaged in `Bridge.lean`'s
`temporal_bridge`, but not in the theorem named "EPP correspondence". Same in
`epp_correspondence_complete` (`EPPCompletion.lean:62-70`). Anyone citing
`epp_correspondence` as "the mechanized Theorem" gets a strictly weaker statement than
the paper's item (3). Trivial fix: add the `project_glue_eq` conjunct (quantified over an
arbitrary compatible `F`).

## 3. Resolved-first verdicts diverge from the deployed verifier (documented, keep visible)

Lean: `isViolation S m := resolved ∧ ¬good` (`EPP.lean:83`) — a message with a wrong
sender/spurious predecessor but a *missing* predecessor is `Unknown`, never `Violation`.
`proof.tex` Def. 3 instead says role conformance "returns Violation on mismatch"
immediately (immutable fields, no predecessors needed).

SPEC-014 ADR-602 acknowledges this deliberately: the deployed R5 algebra is *eager*
valid-is-sticky, so it can emit a **provisional Violation later superseded by Valid** —
behavior the Lean model cannot exhibit, and which makes `violation_stable`
(`EPP.lean:113`) **false of the deployed verifier before resolution**. Within the
theorems' hypotheses this never bites (closed configurations / causally-closed runs are
fully resolved, where the two semantics coincide), but:
- `proof.tex` Def. 3 and the Lean model genuinely disagree on partial stores; the TeX
  should say which semantics it means (it currently states the eager one while the
  mechanization it advertises implements the resolved-first one).
- `EPP.lean`'s header would benefit from one sentence citing ADR-602.

## 4. The obligations model (`EPPCompletion.lean`) is stronger and narrower than the paper's

`dischargedFor O S r := ∀ w, req r w → S w ∧ isValid P S w` (`EPPCompletion.lean:28-29`)
against `proof.tex` Def. completion, which distinguishes three kinds:
1. required performative **present** (no validity demanded) — Lean demands `Valid` too
   (strengthening on both sides of the correspondence; theorems remain coherent, but the
   mechanized notion of "complete" is not the paper's);
2. sealed `(all role[*])` members present **and Valid** — matches;
3. pooled `(any role[*])` — "at least one occupant", a *disjunctive* obligation. The Lean
   model cannot express this: `req` names individual required witnesses, so an `(any)`
   obligation must be modeled by pre-choosing its occupant. Two locally-complete runs
   discharging the same pooled obligation via **different occupants** — a legitimate
   scenario under the paper's definition — is outside the model, since the single shared
   `O` forces a common witness.

The header's claim that the model "captures, uniformly" all three (`EPPCompletion.lean:7-9`)
overclaims for (1) and (3). Also note (Seal) is modeled *by fiat*: sharing one `O` across
roles assumes cast agreement rather than stating it as a checkable compatibility condition —
the docstring says so, but it means `completeness_completion` cannot detect cast
disagreement even in principle.

Minor API wart: `epp_correspondence_complete` takes `hcl`, `hsafe` *and*
`hc : pComplete …` although `hc` already contains both (`pComplete := pSafe ∧ closedCfg ∧ …`).
Derive them from `hc` instead.

## 5. `type_opacity_indistinguishability`: the formal "no decider" is weaker than the prose

The final conjunct (`Splice.lean:208-210`) quantifies over
`f : (Msg → Prop) → (Msg → Msg → Prop) → Msg → Verdict` — deciders reading only the
*held-message set* and the citation relation. The docstring claims "no function of `r`'s
observation … computes `m`'s verdict", but `r`'s observation also includes the held
messages' performatives/senders/recipients. Those agree across the two worlds — that is
exactly `held_types_agree` (`Splice.lean:176-181`), proved but supplied as a separate
conjunct rather than as an argument to `f`. The stronger statement (give `f` the held-type
map too, e.g. an extra `Msg → Option Perf` argument defined on the projection) is provable
with the same two-line proof and would match the prose. As stated, the impossibility covers
a smaller class of deciders than advertised.

Similarly, "openings" in §2b are an interpretive gloss: the model's store cannot distinguish
"holds a type-tag" from "holds the full message" — `openStore` (`Splice.lean:339`) contains
full messages. The genuine mechanized content is the factoring theorem
`safety_reads_types_only` (the verdict reads the store only through `resolvedD` +
`predTypesPresentD`), which *justifies* the SPEC-017 opening story but does not model
openings. Fine as-is; the docstrings already lean this way, but README line 148
("carries exactly the predecessor type", "Merkle-over-fields") attributes more to
`openings_suffice` than the Lean statement contains.

## 6. `reconcile_global`'s "all three verdicts agree" is trivial on its domain

Under its own hypotheses (`closedCfg` + `pSafe`), every `m ∈ C` is resolved and good,
hence `Valid` — so the `Unknown` and `Violation` components of the "verdict equality"
triple (`EPP.lean:177-187`) are equivalences between propositions that are both false on
the domain of application. This matches `proof.tex` (same hypotheses there) and the
lemma does real work (the Violation-iff is what powers `soundness_safety`), but the header
sentence "the reconciliation lemmas establish genuine *verdict equality* (all three …
agree)" (`EPP.lean:13-15`) invites over-reading: there are no reachable Violation or
Unknown states being reconciled. Suggest one clarifying sentence. (The place where a
non-trivial three-way verdict statement *does* live is `bridge_stability` over partial
stores, and `unknown_means_not_yet_arrived` for the Unknown case.)

## 7. CI does not enforce the axiom claim for the EPP modules

`proof.tex:370-372` claims "mechanized in Lean 4 (no sorry; axioms propext,
Classical.choice, Quot.sound)". True today (verified by probe), but unenforced:
- `AxiomAudit.lean` / `scripts/check-axioms.sh` cover only CON-510..516 — nothing from
  `EPP.lean`, `EPPCompletion.lean`, `Projectability.lean`, `Splice.lean`, `Bridge.lean`.
- The inline `#print axioms` at the ends of `Projectability.lean`, `Splice.lean`,
  `Bridge.lean` are informational output only; nothing parses or fails on them, and
  `EPP.lean` / `EPPCompletion.lean` have none at all.
- `Splice.lean` imports `Batteries.Tactic.Lint`, so the import surface is no longer
  Lean-core-only; a future edit could silently pull in an axiom.

Recommend adding the headline EPP theorems to `AxiomAudit.lean` (the shell script picks
them up automatically per its header).

## 8. Smaller observations (no action strictly required)

- **`Proto.legalPred` and `Proto.clause` are unlinked.** Nothing requires the clause to
  mention only legal predecessor types. Harmless for all present theorems (the clause is
  only ever evaluated on actual predecessors, which `noSpurious` constrains), but the model
  admits protocols where every message of some type is unsatisfiable. Worth a comment.
- **The abstract EPP model is disconnected from the concrete `CBCL.Verify` development.**
  The claim that `resolved` mirrors `MessageStore.lookup` semantics (and that `predRel`
  is "the bare hash") lives only in `Splice.lean`'s prose header (§"Definitions reused —
  stated, not re-proved"). The paper's Agreement condition (equal hash ⇒ identical message)
  is inherent in the predicate model rather than proved from `contentHash_injective`.
  Honest as written, but the two Lean developments verify different objects and the bridge
  between them is informal.
- **The converse of Theorem 1 is existential by design** (`causal_locality_necessary`,
  one witness protocol), matching the docstring "as the review requires". A per-protocol
  converse would be false in general (a violating `legalPred` edge need not be exercisable
  by any run), so the existential form is the right call — the docstring could say *why*.
- **`Schedule.bounded`** (`Bridge.lean:58`) assumes an endpoint never holds a message
  outside its projection — part of the definition of "conformant execution"; deserves a
  word in the docstring since it excludes misdelivery from the temporal bridge's scope.
- **`resolution_requires_preimage`** keeps an unused hypothesis `_hL` purely to state
  necessity "in the same frame" as sufficiency; the comment says the un-hypothesized fact
  is stronger. Fine — flagged only because keeping an unused hypothesis in an "audited
  statement" trades statement strength for framing symmetry, which is the kind of thing a
  reviewer will ask about.

## Addendum: fresh-context review of `R6DCFLPreservation.lean` (2026-07-10)

After the R6 DCFL mechanisation landed, an independent fresh-context review
(adversarial brief: vacuity, semantic fidelity to `verify_causal`, projection fidelity,
syntax-half honesty, proof hygiene) found the Lean development itself sound — proofs
correct, axiom-clean, the state-collapse regularity argument genuine, REG ⊆ DCFL
legitimate — but confirmed three fidelity defects and two honesty gaps, all remediated
in the same session:

1. **Clause semantics inverted (severe, fixed).** `preds` were read conjunctively
   ("all must hold"); `verify_causal` reads the `Single`/`Any` pool disjunctively —
   `protocol.rs` documents `[Single a, Single b]` as `a ∨ b` — with `All` consulted
   only by the fan-in citation route (first `(all …)` decl only). `justified` now
   follows the verifier route by route (root / literal-`begin` / pooled single
   citation / fan-in), with `ex_pool_is_disjunctive` pinning the doc's own example.
2. **Unknown modelled as permanent death (fixed).** The old acceptance rejected
   out-of-order arrival outright, contradicting the valid-sticky lattice
   (`out_of_order_is_unknown_then_valid`). Now two languages: `CausalTrace`
   (arrival-order) and `StoreTrace` (order-free, "every message eventually Valid" —
   the deployed accepted language), with `causalTrace_storeTrace` embedding the first
   in the second and `ex_out_of_order_store` witnessing strictness.
3. **Undeclared performatives (fixed).** Were never enabled; `verify_causal` treats
   them as unconstrained (`Valid`). Now `enabled` returns `true` on a `find?` miss,
   and the finite carrier is the *relevant*-name universe (declared names plus every
   clause-mentioned name) since undeclared-but-cited names can justify a pool member.
4. **`projection_adds_no_recogniser` overstated (reworded).** It is `rfl` by
   construction and would hold for any step-list transformation; the docstring, README
   and `proof.tex` now say so, point at the regularity instances as the substantive
   local statements, and note the ADR-604 divergence (the shipped composition verifies
   against the global protocol; the step-filtered projection is the paper's object).
5. **Syntax half (fixed + reworded).** `rolesClause` now transcribes CON-600's
   inner-list, ≥1-decl shape; all `IsSExpr` theorems are labelled typechecking-level
   (`IsSExpr` is universal — they pin constructors, not the CON-600 shape, which is
   `role.rs` + property tests).

Also disclosed in the file header: duplicate step names are inexpressible in Rust
(`BTreeMap`) and first-match-shadowed here; `begin` is an ordinary name plus the
store-free literal-citation route. Gates after remediation: build green, 0 sorries,
50 theorems audited, standard axioms only.

## Verification performed

- `lake build` — success (63 jobs), zero sorries (`lean4-skills-sorry-analyzer`, 30 files).
- `#print axioms` probe over all headline theorems — standard kernel axioms only.
- Hand-checked: `localres`, `predTypesPresent_mono/proj/glue`, `reconcile_global`,
  `completeness_safety`, `reconcile_glue`, both round-trip lemmas, both counterexamples
  (`Projectability.Counterexample`: causal-locality failure at `(py, px, rC)` and
  permanent Unknown of `my`; `Splice.Example`: world pair differing only in `perf b`,
  Valid/Violation split, `held_types_agree`), `bridge_stability` monotonicity chain.
- Cross-checked theorem-name references in SPEC-014 §719-815 — all names resolve and
  match the cited files.
