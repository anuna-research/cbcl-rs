---
id: BUG-002
title: "`install_preserves_core` declares `verifyR3 d = true` as a hypothesis but the proof does not use it"
severity: S3
priority: P2
status: fixed
reported-by: agent:claude-opus-4-7
assigned-to: agent:hugo
fixed-by: agent:claude-opus-4-7 (Claude Code)
reported-date: 2026-04-18
fixed-date: 2026-04-18
fix-ref: plans/FIX-LEAN-AUDIT.spl (task bug-002)
component: lean-cbcl/LeanCbcl/R3CorePreservation.lean
---

# BUG-002: `install_preserves_core` declares `verifyR3 d = true` as a hypothesis but the proof does not use it

**Severity:** S3 (Moderate)
**Priority:** P2
**Status:** new
**Reported by:** agent:claude-opus-4-7 (Claude Code, 1M-context Opus 4.7)
**Assigned to:** unassigned

## Specification Reference

- **Violates:** spec-gap — no REQ-### formalises the semantic content of "installation safety" for R3. The paper's Theorem 11 serves as the de facto specification but does not bind the Lean formalisation to keep the R3 premise load-bearing.
- **Paper claim affected:** `paper/langsec-workshop-paper.tex:376` — "**Theorem 11** (Installation Safety). *Installing an R3-verified dialect into a well-formed agent preserves well-formedness.*"
- **Related:** `Agent.lean:26` defines `Agent.wellFormed` as `∃ rest, a.dialects = baseDialect :: rest` — i.e. only "the base dialect is first in the dialect list." This structural invariant is the full content of "well-formedness" in the current formalisation.
- **Related (non-affected):** `core_performative_not_in_r3_dialect` at `R3CorePreservation.lean:40` is the theorem that genuinely expresses R3's core-preservation property; it is load-bearing and correctly uses `verifyR3 d = true`. The paper's Theorem 10 is backed by this theorem and is not affected by this bug.

## Environment

- Repository: `cbcl-rs` at commit `c821a68` on branch `main`
- Lean toolchain: Lean 4.27
- Build status: `lake build` passes clean; defect is a signature-vs-proof discrepancy detectable only by reading source
- Detection environment: static inspection

## Steps to Reproduce

1. Open `cbcl-rs/lean-cbcl/LeanCbcl/R3CorePreservation.lean`.
2. Read the theorem at line 53:

    ```lean
    /-- Installing an R3-verified dialect preserves well-formedness. -/
    theorem install_preserves_core
        (a : Agent) (d : Dialect)
        (hwf : a.wellFormed)
        (_hr3 : verifyR3 d = true) :
        (a.installDialect d).wellFormed :=
      Agent.installDialect_preserves_wellFormed a d hwf
    ```

3. Observe: the parameter `_hr3` is **underscore-prefixed**, a Lean convention for "declared but not used." The proof body is `Agent.installDialect_preserves_wellFormed a d hwf`, which accepts only `a`, `d`, and `hwf` — the R3 verification result is not threaded through the proof in any form.
4. Open `cbcl-rs/lean-cbcl/LeanCbcl/Agent.lean` and read `Agent.installDialect_preserves_wellFormed` at line 42:

    ```lean
    theorem Agent.installDialect_preserves_wellFormed
        (a : Agent) (d : Dialect) (hwf : a.wellFormed) :
        (a.installDialect d).wellFormed := by
      obtain ⟨rest, hrfl⟩ := hwf
      exact ⟨rest ++ [d], by simp [Agent.installDialect, hrfl]⟩
    ```

5. Confirm: this underlying theorem proves well-formedness for **any** dialect — the proof is purely structural (`base :: rest ++ [d] = base :: (rest ++ [d])`). The "R3-verified" qualifier in `install_preserves_core` is cosmetic.
6. Try swapping `verifyR3 d = true` with a deliberately-false hypothesis such as `verifyR3 d = false` in the theorem statement and re-run `lake build`. Expected: proof still succeeds, because the hypothesis is discarded. (This is not required for the bug to be valid, but demonstrates the vestigial nature of the premise.)

## Expected Behaviour

For the paper's Theorem 11 ("Installing an *R3-verified* dialect into a well-formed agent preserves well-formedness") to hold as written, the R3 verification must be load-bearing in the Lean proof. Either:

- The `Agent.wellFormed` invariant should encode an R3-relevant property (e.g. "no installed dialect defines a core performative"), so that preservation under installation genuinely requires the new dialect to be R3-verified, **OR**
- The theorem should be narrowed in the paper to match what the Lean proof actually establishes: "Installing *any* dialect into an agent whose first dialect is `baseDialect` preserves the property that the first dialect is `baseDialect`."

Currently, neither holds: the Lean proof does the weaker (structural) claim while carrying an unused R3 premise that misrepresents what the theorem proves.

## Actual Behaviour

The theorem type-checks and the paper's Theorem 11 is technically true (an unused hypothesis in a true statement does not make the statement false). However, the R3 hypothesis provides no eliminative content: a reviewer or reader would reasonably infer that `verifyR3 d = true` is what makes `a.installDialect d` well-formed, when in fact the preservation is purely a list-cons preservation and holds for any `d` — R3-verified or not.

## Evidence

- `R3CorePreservation.lean:53-59` — theorem as above.
- `Agent.lean:42-46` — the underlying theorem does not take any R3-like hypothesis.
- `Agent.lean:26-27` — the definition of `Agent.wellFormed`:

    ```lean
    def Agent.wellFormed (a : Agent) : Prop :=
      ∃ rest, a.dialects = baseDialect :: rest
    ```

  This is provably preserved by any list append that does not touch the head, independent of R3.
- Full audit with reasoning: `cbcl-paper/plans/lean-audit-findings.md` (finding G2).

## Root Cause (initial analysis)

- **Category:** implementation-error + design-error. The Lean formalisation defines `Agent.wellFormed` as a trivial structural predicate (design-error: the invariant is too weak to be load-bearing with respect to R3) and then wires an R3 premise into `install_preserves_core` that cannot be discharged because the predicate does not consume it (implementation-error: the premise is declared but not threaded).
- **Contributing factor:** the load-bearing theorem for R3 is actually `core_performative_not_in_r3_dialect` (R3CorePreservation.lean:40), which is soundly proved and genuinely uses `verifyR3`. `install_preserves_core` appears to exist to echo the paper's Theorem 11 but does so with the wrong `wellFormed` definition for the claim.
- **Why tests didn't catch it:** this is a type-level vestigial hypothesis. No test on the extracted Rust parser or on runtime behaviour could surface it. Cross-model adversarial review against the paper's Theorem 11 prose is the only detection method.

## Resolution (proposed — awaiting decision)

Two coherent resolutions:

**Option A — strengthen `Agent.wellFormed` to encode an R3 invariant.** Redefine `Agent.wellFormed` as (in prose): "the base dialect is first AND no non-base dialect defines a core performative name." With that stronger invariant, `install_preserves_core` becomes a genuine load-bearing composition: preservation requires `verifyR3 d = true` to discharge the "no core redefinition" clause for the newly-installed dialect. This matches the paper's Theorem 11 prose and restores load-bearing use of R3.

**Option B — narrow the Lean theorem to match the actual structural proof.** Drop the `_hr3` premise from `install_preserves_core`, rename the theorem (e.g. `installDialect_preserves_base_head`) to reflect the purely structural content, and adjust any downstream references. The paper's Theorem 11 wording would become out-of-sync with the Lean theorem, which — given the paper is already published — should be noted in an erratum or deferred to a future revision.

**Recommended:** Option A. It (i) makes the Lean theorem match the published paper's prose rather than diverging from it, (ii) makes R3 genuinely load-bearing at the installation boundary, and (iii) composes cleanly with `core_performative_not_in_r3_dialect` (R3CorePreservation.lean:40), which is already the proof of the core invariant. The work is bounded — redefine `Agent.wellFormed`, update `Agent.new_wellFormed` and `Agent.installDialect_preserves_wellFormed`, and rewrite `install_preserves_core` to thread `_hr3` through.

- **Fix landed (2026-04-18):** Option A (revised — see review below). `Agent.wellFormed` now encodes the compound invariant as `∃ rest, a.dialects = baseDialect :: rest ∧ (∀ d ∈ rest, d.noCoreRedefinition)`. Clause (ii) applies only to *non-first* dialects (positional, not name-based); the head is pinned to the literal `baseDialect` constant by clause (i). `Agent.installDialect_preserves_wellFormed` takes `hNoCore : d.noCoreRedefinition` (no disjunctive exemption). `install_preserves_core` takes two load-bearing premises: `hr3 : verifyR3 d = true` and `hname : d.name ≠ "cbcl-base"`. Both are discharged into `r3_no_core_redefinition` to prove `d.noCoreRedefinition`. A concrete regression test (`spoofedBaseDialect`, `spoofed_passes_verifyR3`, `spoofed_fails_noCoreRedefinition`) witnesses the loophole closure: `verifyR3` alone admits a name-spoofed dialect redefining `tell`, but the spoof fails `noCoreRedefinition`, so the `hname` premise in `install_preserves_core` is genuinely load-bearing.
- **Post-fix review (2026-04-18):** an initial version of this fix used a `Dialect.coreSafe` predicate with a name-based disjunctive exemption (`d.name = "cbcl-base" ∨ ...`). Cross-model review flagged this as unsound: it admits a spoofed dialect (different performatives, same name) to pass the invariant, and `Agent.findPerformativeDialect` (searching the reversed `dialects` list) would then resolve core names to the spoofed definition. The fix was revised to use the positional guarantee above, dropping `coreSafe` in favour of a non-disjunctive `Dialect.noCoreRedefinition`.
- **Verified by:** `lake build` (0 errors, 35/35 jobs). Load-bearing property is witnessed by `install_no_core_redefinition` (positive) and `spoofed_fails_noCoreRedefinition` (negative).
- **Regression tests added:** `install_no_core_redefinition`, `spoofed_passes_verifyR3`, `spoofed_fails_noCoreRedefinition` — all in `R3CorePreservation.lean`.

## AI Detection Context

- **Detecting model:** Claude Opus 4.7 (1M-context) via Claude Code
- **Detection method:** adversarial review of the Lean formalisation against the paper's Theorem 11 wording, cross-referenced with `Agent.wellFormed` and the underlying theorem `Agent.installDialect_preserves_wellFormed`
- **Confidence:** high — the `_hr3` underscore prefix is a definitive marker of unused parameter; the underlying theorem's signature confirms R3 is not threaded; and the structural content of `Agent.wellFormed` is directly observable
- **Session context:** `cbcl-paper/plans/lean-audit-findings.md`; hence plan `cbcl-paper/plans/lean-audit-basis-gotchas.spl`
- **Review tier:** Tier 2 (core business logic — formal verification of a safety invariant) — cross-model review recommended before accepting the chosen resolution

## Notes for Triage

- Sister bugs: BUG-001 (`allSExpr_wellFormed` vacuous) and BUG-003 (`dcfl_preserved` vestigial hypotheses). Same audit session, same root-cause pattern: paper wording implies load-bearing composition through a premise that the Lean proof does not actually consume.
- The paper is already submitted; no camera-ready change is possible. The fix is to restore honesty in the formalisation so that (a) future extensions of the paper can cite the theorem without erratum, and (b) the Lean artefact is correct in isolation regardless of paper state.
- Option A's strengthened `Agent.wellFormed` would also materially improve the DCFL-preservation story (BUG-003) by giving that theorem a non-trivial well-formedness premise to actually use. The two fixes are therefore coupled and should be planned together.
