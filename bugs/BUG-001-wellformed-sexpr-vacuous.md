---
id: BUG-001
title: "`allSExpr_wellFormed` theorem is vacuous — `WellFormedSExpr` predicate admits every `SExpr`"
severity: S3
priority: P2
status: new
reported-by: agent:claude-opus-4-7
assigned-to: unassigned
reported-date: 2026-04-18
component: lean-cbcl/LeanCbcl/Parser.lean
---

# BUG-001: `allSExpr_wellFormed` theorem is vacuous — `WellFormedSExpr` predicate admits every `SExpr`

**Severity:** S3 (Moderate)
**Priority:** P2
**Status:** new
**Reported by:** agent:claude-opus-4-7 (Claude Code, 1M-context Opus 4.7)
**Assigned to:** unassigned

## Specification Reference

- **Violates:** spec-gap — the Lean formalisation does not have a formal REQ-### that captures what `WellFormedSExpr` is intended to rule out. The defect is discovered by cross-referencing the camera-ready paper's published claim (`paper/langsec-workshop-paper.tex` line 323) with the Lean definition.
- **Paper claim affected:** `paper/langsec-workshop-paper.tex:323` — "A universal well-formedness theorem (`allSExpr_wellFormed`) additionally proves by structural induction that *every* SExpr value satisfies the inductive `WellFormedSExpr` predicate, ensuring the parser can only produce structurally valid output."
- **Related:** no TEST-### exists that would have caught this; no contract (CON-###) formalises the semantic content of `WellFormedSExpr`.

## Environment

- Repository: `cbcl-rs` at commit `c821a68` on branch `main`
- Lean toolchain: `lean-toolchain` (Lean 4.27 per project setup)
- Build status: `lake build` passes clean (35 jobs) — defect is not a compilation failure but a semantic hollowness
- Detection environment: static inspection of Lean sources; no dynamic execution required

## Steps to Reproduce

1. Open `cbcl-rs/lean-cbcl/LeanCbcl/Parser.lean`.
2. Locate the inductive definition of `WellFormedSExpr` at line 142:

    ```lean
    inductive WellFormedSExpr : SExpr → Prop where
      | atom : ∀ a, WellFormedSExpr (.atom a)
      | list : ∀ xs, (∀ e, e ∈ xs → WellFormedSExpr e) → WellFormedSExpr (.list xs)
    ```

3. Locate the inductive definition of `SExpr` in `cbcl-rs/lean-cbcl/LeanCbcl/SExpr.lean`.
   Observe that `SExpr` has exactly two constructors: `.atom a` (where `a : Atom`) and `.list xs` (where `xs : List SExpr`).
4. Observe that `WellFormedSExpr` provides one introduction rule per `SExpr` constructor, each rule accepting any inhabitant of the corresponding shape without additional constraints.
5. Locate the theorem `allSExpr_wellFormed` at `Parser.lean:280`:

    ```lean
    theorem allSExpr_wellFormed : ∀ (e : SExpr), WellFormedSExpr e := ...
    ```

6. Observe that the proof is a direct structural recursion over `SExpr` using `SExpr.rec`, with no side-conditions.
7. Conclude: `WellFormedSExpr` is isomorphic to the constant-`True` predicate on `SExpr`. The theorem is mathematically correct but carries no eliminative content — there is no `SExpr` value for which `WellFormedSExpr` fails.

## Expected Behaviour

The published paper states (`langsec-workshop-paper.tex:323`) that `allSExpr_wellFormed` "ensures the parser can only produce structurally valid output." For that claim to be load-bearing, the `WellFormedSExpr` predicate must rule out at least one malformed `SExpr` value — for example, by constraining list depth, atom content, or symbol validity. A meaningful `WellFormedSExpr` would reject at least some inhabitants of the type `SExpr` that the parser is not expected to produce.

## Actual Behaviour

`WellFormedSExpr e` holds for every `e : SExpr` by construction. The inductive predicate has exactly one constructor per shape-variant of `SExpr`, so the predicate is the identity on inhabitation. The theorem `allSExpr_wellFormed` is provable by trivial structural recursion and eliminates no inputs. The paper's claim that it "ensures the parser can only produce structurally valid output" is not supported by the theorem as stated; every `SExpr` inhabitant is "well-formed" in this sense, including hypothetically parser-unreachable values.

The load-bearing parser-correctness results in the same file are `parseMessage_sound` and `parseMessage_complete` (MessageParser.lean:137, 162), which are stated against a genuinely non-trivial `ValidMessageGrammar`. Those theorems are not affected by this defect.

## Evidence

- `Parser.lean:142-144` (definition of `WellFormedSExpr`):

    ```lean
    inductive WellFormedSExpr : SExpr → Prop where
      | atom : ∀ a, WellFormedSExpr (.atom a)
      | list : ∀ xs, (∀ e, e ∈ xs → WellFormedSExpr e) → WellFormedSExpr (.list xs)
    ```

- `Parser.lean:280-290` (proof of `allSExpr_wellFormed`): uses `@SExpr.rec` with `(fun a => .atom a)` and `(fun xs ih => .list xs ih)` — structural identity.
- Full audit with reasoning: `cbcl-paper/plans/lean-audit-findings.md` (finding G1).

## Root Cause (initial analysis)

- **Category:** implementation-error — the Lean definition of `WellFormedSExpr` is strictly weaker than what the paper's prose implies. The intent was presumably a structural-validity predicate that rules out malformed shapes (e.g. symbols containing disallowed characters, keyword atoms with delimiter chars — noting that such a predicate exists piecemeal elsewhere, e.g. `SafeSymbol` in `Serializer.lean`). The actual predicate made no such restrictions, producing a theorem that is true but empty.
- **Contributing factor:** no REQ-### or CON-### formalises the semantic content that `WellFormedSExpr` is supposed to capture, so the predicate had no external obligation to discharge. This is also a spec-gap (dimension 2): the formalisation was written without a specification of what it should rule out.
- **Why tests didn't catch it:** the defect is not a functional incorrectness that a test could witness; it is a weak theorem statement. Mutation testing of the Lean source would not surface it either. Only adversarial review against the paper's prose — or the kind of audit that motivated this bug report — can surface a vacuous theorem.

## Resolution (proposed — awaiting decision)

Two coherent resolutions exist; the choice is a specification decision, not a purely technical one.

**Option A — narrow the theorem to match existing semantics.** Keep `WellFormedSExpr` as is but rename it (e.g. `IsSExpr`) and remove the paper's over-reaching claim. This is an honest fix but loses any parser-output invariant beyond "the parser returns an `SExpr`."

**Option B — strengthen the predicate.** Redefine `WellFormedSExpr` to encode a non-trivial structural invariant that the parser is supposed to preserve. Candidates (derivable from the existing code):
  - Symbols satisfy `SafeSymbol`.
  - Keyword atoms contain no delimiter characters (mirrors `RoundTrippable₂` correction in `Serializer.lean:215`).
  - String atoms respect the parser's internal encoding constraints.
  Then prove `parseSExpr_wellFormed` (currently trivially discharged by `allSExpr_wellFormed`) using the parser's actual structural guarantees.

**Recommended:** Option B for the parts the parser genuinely guarantees (symbols and keywords), with a `TEST-###` that demonstrates `WellFormedSExpr` rejects at least one specific malformed value. This makes the predicate load-bearing and the theorem non-vacuous.

- **Fix:** to be decided per option above
- **Verified by:** TEST-### to be written — must exhibit at least one concrete `SExpr` value for which `WellFormedSExpr` fails
- **Regression test added:** pending fix

## AI Detection Context

- **Detecting model:** Claude Opus 4.7 (1M-context) via Claude Code
- **Detection method:** adversarial review of the Lean formalisation against the camera-ready paper's published verification claims, motivated by a Basis Research blog post ("Building an Unverified Compiler with Agents", https://www.basis.ai/blog/verified-compiler/) that flags vacuous-theorem gotchas in AI-produced proofs
- **Confidence:** high — directly observed in the Lean source; the predicate definition and the `SExpr` constructors were read together and verified by reductio to produce an inhabitation that the predicate rejects (none exists)
- **Session context:** `cbcl-paper/plans/lean-audit-findings.md`; hence plan `cbcl-paper/plans/lean-audit-basis-gotchas.spl`
- **Review tier:** Tier 2 (core business logic — formal verification of a protocol) — per USDD protocol §Multi-Model Cognitive Diversity, before accepting a fix, the fixed Lean should be cross-reviewed by a different model family with an adversarial prompt

## Notes for Triage

- The paper with this claim has already been accepted and submitted (LangSec '26 camera-ready), so the immediate priority is **not** fixing the published claim. The priority is fixing the formalisation so that a future revision, extended paper, or arXiv v2 can replace the misleading wording with a truthful, load-bearing claim.
- The defect does not affect runtime correctness of `cbcl-rs` or any extracted binary. It is purely a claim-vs-theorem mismatch inside the Lean formalisation.
- This bug is one of three filed from the same audit session; the others are BUG-002 (`install_preserves_core` vestigial hypothesis) and BUG-003 (`dcfl_preserved` vestigial hypotheses and `def`-vs-`theorem` mismatch). They share a root-cause pattern — paper wording implies a load-bearing composition that the Lean proofs do not establish — and should be triaged together.
