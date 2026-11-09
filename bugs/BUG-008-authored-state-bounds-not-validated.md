---
id: BUG-008
title: Typed authored installation omits native state-bound validation
severity: S2
priority: P1
status: fixed
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: lean-cbcl/LeanCbcl/StateAuthoredBindings.lean
---

# BUG-008: Typed authored installation accepts invalid state bounds

The modeled authored metadata gate checked field counts against supplied bounds
but did not check whether those bounds were positive tightenings of the native
defaults. The finite live oracle also used a fixed default, hiding this missing
installation precondition. This weakens the installation correspondence required
by [[SPEC-038-lvar-state-kernel#REQ-3810]] and the acceptance evidence for
[[SPEC-038-lvar-state-kernel#TEST-3806]].

## Reproduction and evidence

Expose `max-list` in the finite oracle request. Use the existing four-element
valid table with `max-list = 65`. Native `r7_violations` rejects it as exceeding
the default; the old modeled table checker accepts four elements under limit 65.
The directed live test failed with Lean `installed: true` versus Rust
`installed: false` (captured in `/tmp/spec038-bound-gate-red.log`).

Native checks are at `crates/cbcl-core/src/r7.rs` in `r7_violations`, before state
clause validation: bounds cannot exceed their defaults and must be positive.
`StateBounds::default` sets list length 64, fields 32, string bytes 2048 and
numeric magnitude 10^12. The typed authored gate omitted those checks.

An earlier hypothesis that the model's 64-element cap was itself incorrect was
**disproved**: a 65-element table with an increased state bound is rejected by
native R7. The cap remains correct for installed dialects. That failed hypothesis
is not evidence for changing the language or widening native bounds.

## Required correction

Implement the same bounds predicate in the typed installation gate and oracle;
retain configured-limit checks and the existing 64-element finite carrier cap.
Prove equality with the native rejection conditions. Test zero and over-default
bounds before source compilation, and keep field-count rejection fixtures valid
in every other bound so they exercise their intended condition.

Native Rust behavior is unchanged. Literal wire parsing and native metadata
extraction remain separate correspondence boundaries.

## Verified correction

The aggregate Lean build and Batteries environment linter pass, with 1843
allowlisted theorem audits. All six live Rust/Lean oracle suites pass with
`PROPTEST_CASES=512` and `PROPTEST_RNG_SEED=380038`. Selected parser, finite,
state, export and corpus suites pass. Focused proof mutations reject bypassing
the authored bounds gate and corrupting default/positivity predicates.

Removing the actual native R7 default-list-bound guard makes the directed
live oracle comparison fail. `StateInstalledBounds.native_gate_refinement`
proves equality with the modeled native rejection conditions;
`StateAuthoredSourceProvenance.prepared_bounds` derives the gate from successful
preparation. Literal Rust extraction remains outside this theorem.
