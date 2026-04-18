---
id: BUG-003
title: "`dcfl_preserved` declares `verifyR3` and `wellFormed` as premises but uses neither"
severity: S2
priority: P1
status: fixed
reported-by: agent:claude-opus-4-7
assigned-to: agent:hugo
fixed-by: agent:claude-opus-4-7 (Claude Code)
reported-date: 2026-04-18
fixed-date: 2026-04-18
fix-ref: plans/FIX-LEAN-AUDIT.spl (task bug-003)
component: lean-cbcl/LeanCbcl/DeterministicUnion.lean
---

# BUG-003: `dcfl_preserved` declares `verifyR3` and `wellFormed` as premises but uses neither

> **Revision note (2026-04-18):** an earlier version of this report additionally flagged that the declaration uses `def` rather than `theorem`. That framing was incorrect: `IsDCFL` is defined at `DetParser.lean:62` as a `structure` carrying a `parser : DetParser` field, placing it in `Type` rather than `Prop`. Lean rejects `theorem _ : IsDCFL _` with "type of theorem is not a proposition." The `def` surface form is correct for this return type; only refactoring `IsDCFL` into a `Prop`-only statement would enable `theorem`. The def-vs-theorem framing has been removed from this report; the vestigial-premise finding (the substantive defect) is retained unchanged.

**Severity:** S2 (Major)
**Priority:** P1
**Status:** new
**Reported by:** agent:claude-opus-4-7 (Claude Code, 1M-context Opus 4.7)
**Assigned to:** unassigned

## Specification Reference

- **Violates:** spec-gap — no REQ-### formalises the composition "R3 verification + well-formedness → DCFL preservation." The paper's Section 4 (DCFL preservation argument) and its final sentence at `langsec-workshop-paper.tex:398` serve as the de facto specification.
- **Paper claim affected:** `paper/langsec-workshop-paper.tex:398` — "This argument is fully mechanized in Lean~4. Theorems 2--3 establish parser correctness, 4--7 verify R1, 8--9 verify R2, and 10--11 verify R3. The deterministic-union construction is proven by `agentDetParser_agrees`, which shows that the combined DPDA agrees with the boolean decider for agents with unique dialect names (`namesUnique`). The final theorem `dcfl_preserved` composes these results: installing a fresh R3-verified dialect preserves DCFL membership."
- **Related, and NOT affected:** `agentDetParser_agrees` (DeterministicUnion.lean:1215) and `namesUnique_installDialect` (DeterministicUnion.lean:1562) are load-bearing and correctly stated. The defect is confined to `dcfl_preserved` and to the paper's prose about "composing" through R3.

## Environment

- Repository: `cbcl-rs` at commit `c821a68` on branch `main`
- Lean toolchain: Lean 4.27
- Build status: `lake build` passes clean; defect is a signature/declaration-form discrepancy detectable only by reading source
- Detection environment: static inspection

## Steps to Reproduce

1. Open `cbcl-rs/lean-cbcl/LeanCbcl/DeterministicUnion.lean`.
2. Read the declaration at line 1574:

    ```lean
    def dcfl_preserved (a : Agent) (d : Dialect)
        (hnu : a.namesUnique)
        (_hwf : a.wellFormed)
        (hFresh : d.name ∉ a.dialects.map Dialect.name)
        (_hR3 : verifyR3 d = true) :
        IsDCFL (agentLanguage (a.installDialect d)) :=
      agentLanguage_isDCFL (a.installDialect d) (namesUnique_installDialect hnu hFresh)
    ```

3. Observe the defect: both `_hwf` and `_hR3` are underscore-prefixed, and the right-hand side (`agentLanguage_isDCFL ... (namesUnique_installDialect hnu hFresh)`) consumes only `hnu` and `hFresh`. `_hwf` and `_hR3` are declared but not threaded through the proof.
4. Try replacing `_hR3 : verifyR3 d = true` with `_hR3 : verifyR3 d = false` and rebuild. Expected: build still succeeds, because the hypothesis is discarded. (Not required for the bug to be valid.)

Note: the declaration uses `def` rather than `theorem`. This is correct and not a defect — the return type `IsDCFL ...` is a `structure` in `Type` (see `DetParser.lean:62`), not a `Prop`, so `theorem` would fail to type-check.

## Expected Behaviour

For the paper's composition claim ("installing a fresh *R3-verified* dialect preserves DCFL membership") to be mechanized honestly, the Lean declaration should be structured so that either `verifyR3 d = true` is discharged against a `wellFormed` invariant that materially uses R3 (see BUG-002 Option A), or the R3 and `wellFormed` premises are dropped and the paper's prose is narrowed to match what is proved, namely: "installing a fresh dialect (with a name not already installed) into an agent with unique dialect names preserves DCFL membership of the agent's language."

The actually-proved claim — conditional on `namesUnique` and `hFresh` — is itself a correct and genuinely load-bearing DCFL closure result. It simply does not compose through R3 or through the current `wellFormed` predicate.

## Actual Behaviour

The declaration type-checks and, because `_hwf` and `_hR3` are unused, the resulting proposition is true regardless of what those premises say. But:

1. The paper's narrative — that `dcfl_preserved` composes R1–R3 verification results with DCFL closure — is not borne out by the Lean proof. The R3 check is not part of the composition. The `wellFormed` premise is not part of the composition.
2. The defect is the most material of the three in this audit session because `dcfl_preserved` sits at the paper's headline mechanisation claim (Section 4, "DCFL Preservation Argument"). A reviewer who opens the source to verify the composition will find that only two of the four declared premises are load-bearing.
3. The correct statement — "for any agent with unique dialect names, installing a dialect with a fresh name preserves DCFL membership" — is strictly stronger in one direction (no R3/wellFormed requirement) and strictly weaker in another (no well-formedness claim), depending on how you frame it.

## Evidence

- `DeterministicUnion.lean:1574-1580` — declaration as above.
- `DeterministicUnion.lean:1562-1572` — `namesUnique_installDialect` shows `namesUnique` + `hFresh` is exactly what is needed:

    ```lean
    private theorem namesUnique_installDialect {a : Agent} {d : Dialect}
        (hnu : a.namesUnique)
        (hFresh : d.name ∉ a.dialects.map Dialect.name) :
        (a.installDialect d).namesUnique := by ...
    ```

- `DeterministicUnion.lean:1215-1221` — `agentDetParser_agrees` is stated under `a.namesUnique`; it does not mention R3 or `wellFormed`.
- Full audit with reasoning: `cbcl-paper/plans/lean-audit-findings.md` (finding G3).

## Root Cause (initial analysis)

- **Category:** design-error (primary) + implementation-error (secondary). The composition story in the paper ties DCFL preservation to R3 verification, but DCFL is a property of the *grammar union*, and R3 constrains *semantic* redefinition of core performatives. R3 has no effect on grammar shape — it is at the wrong layer to participate in a DCFL closure proof. The implementation-error is that the declared premises in `dcfl_preserved` attempt to preserve the paper's narrative at the type level without the proof being able to discharge them.
- **Contributing factor:** the `wellFormed` premise in `dcfl_preserved` also does not materially participate, because the current definition of `Agent.wellFormed` is too weak to be useful as a DCFL composition step (see BUG-002). A strengthened `Agent.wellFormed` (per BUG-002 Option A) would still not connect to DCFL — it constrains core-performative names, not grammar tokens.
- **Why tests didn't catch it:** no test on runtime behaviour could surface this; DCFL membership is a meta-theoretic property proved by construction, not an executable check. Adversarial review against the paper's "composition" prose is the only method.

## Resolution (proposed — awaiting decision)

Three coherent resolutions; the first two align with the paper, the third is the honest scientific fix:

**Option A — drop vestigial premises; rename the claim.** Remove `_hwf` and `_hR3` from the signature and rename if desired to reflect the actual content: "DCFL preservation under unique names and fresh installation." The declaration stays a `def` (its return type `IsDCFL` is not a `Prop`); the definition already constructs a `DetParser` plus soundness and completeness proofs, which is the correct form. The Lean artefact becomes honest and strictly stronger than the paper's claim (it does not require R3). The paper's prose at line 398 becomes out-of-sync — note in an erratum or a followup revision.

**Option B — invent a (different) meaningful composition.** If there is a genuine invariant that DCFL preservation should compose with (e.g. a token-level safety invariant preserved by an R-something verification that is *not* R3), refactor the formalisation to expose it and rewrite `dcfl_preserved` to actually use it. This is high-effort and requires the specification work that was skipped in the original formalisation.

**Option C — fix the paper's prose in a future revision or arXiv v2.** Keep the honest Option A Lean artefact, and in the next public version of the paper, replace "installing a fresh R3-verified dialect preserves DCFL membership" with the actually-proved claim. This is the scientifically correct path but requires publisher coordination.

**Recommended:** Option A + Option C. Fix the Lean artefact now (low effort) so the repository is honest in isolation, and schedule the paper prose fix for the next public revision. Do not pursue Option B unless a genuine token-level invariant is discovered that warrants the engineering cost — manufacturing such an invariant retroactively would itself be a specification anti-pattern (§11 of USDD constitutional principles — "Anti-Slop Bias").

- **Fix landed (2026-04-18):** Option A. `dcfl_preserved` now has signature `(a : Agent) (d : Dialect) (hnu : a.namesUnique) (hFresh : d.name ∉ a.dialects.map Dialect.name) : IsDCFL ...` — both vestigial premises (`_hwf`, `_hR3`) removed. A docstring explains why R3/wellFormed are not premises: DCFL is a closure property of the grammar union and does not compose through R3's semantic-core constraint. The parallel case `decidable_preserved` (same vestigial-premise pattern, same file, line 758) was fixed in the same commit — all three of its premises (`_hwf`, `_hFresh`, `_hR3`) were dropped since decidability of `agentLanguage` holds for any agent unconditionally. The README (lines 93, 98) was updated to narrow the prose claim to match the Lean theorems.
- **Verified by:** `lake build` (0 errors, 35/35 jobs). Load-bearing property of remaining premises: `hnu` is consumed by `namesUnique_installDialect`, which consumes `hFresh`.
- **Paper prose mismatch (unfixed):** the camera-ready paper's claim at line 398 ("installing a fresh R3-verified dialect preserves DCFL membership") is no longer supported by the Lean artefact. The paper is published, so this is noted for the next arXiv revision / extended-version paper (Option C of the original resolution).

## AI Detection Context

- **Detecting model:** Claude Opus 4.7 (1M-context) via Claude Code
- **Detection method:** adversarial review of the Lean formalisation against the paper's Section 4 DCFL composition claim, cross-referenced with `namesUnique_installDialect` and `agentLanguage_isDCFL`
- **Confidence:** high — two underscore-prefixed parameters are a definitive marker of unused premises, and the right-hand side of the `def` consumes only the two non-underscored premises
- **Session context:** `cbcl-paper/plans/lean-audit-findings.md`; hence plan `cbcl-paper/plans/lean-audit-basis-gotchas.spl`
- **Review tier:** Tier 2 (core business logic — the headline formal-verification claim of the paper) — cross-model review strongly recommended before accepting the chosen resolution, per USDD §Multi-Model Cognitive Diversity; because the defect was discovered in a single-model review session, at least one different-family model should independently review the revised declaration

## Review Log

| Date | Reviewer | Finding | Resolution |
|------|----------|---------|------------|
| 2026-04-18 | Cross-model review of initial draft | Reported that the initial draft incorrectly flagged `def` vs `theorem` as a defect and recommended a conversion that cannot type-check, because `IsDCFL` is a `structure` in `Type` (see `DetParser.lean:62`). | The def-vs-theorem framing was removed from the title, steps to reproduce, expected behaviour, resolution Option A, and AI Detection Context. A revision note was added at the top of the report. Severity and priority are unchanged — the substantive defect (vestigial `_hwf` and `_hR3` premises) is retained. |

## Notes for Triage

- This is the most consequential of the three audit bugs (BUG-001, BUG-002, BUG-003). `dcfl_preserved` is the capstone theorem of the paper's verification story; a Lean artefact whose headline theorem carries unused premises is a visible target for a reviewer who opens the repository.
- The paper was accepted (LangSec '26, shepherded) and the camera-ready is submitted, so no pre-publication fix is possible. The priority is to (a) fix the Lean artefact to remove the false narrative, (b) prepare a correct statement of DCFL preservation for an arXiv revision or an extended-version paper, and (c) avoid citing Theorem 11 or the "composition" sentence in future work until the fix is in place.
- This bug is tightly coupled to BUG-002. Any rewrite of `dcfl_preserved` that tries to make `_hwf` load-bearing depends on redefining `Agent.wellFormed` (per BUG-002 Option A). Recommend triaging both together under a single IMPL-### plan.
- Sister bug: BUG-001 (`allSExpr_wellFormed` vacuous) shares the vacuous-theorem root-cause pattern but is scoped to a different file and does not require coordinated fixes with BUG-002/BUG-003.
