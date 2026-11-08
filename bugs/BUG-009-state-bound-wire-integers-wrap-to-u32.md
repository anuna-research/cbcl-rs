---
id: BUG-009
title: Oversized state-bound wire integers wrap into valid defaults
severity: S2
priority: P1
status: fixed
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-parser/src/state_parser.rs
---

# BUG-009: Wire state bounds silently truncate before installation checks

The state-bound parser recognized a positive signed integer and cast it with
`as u32` for `max-list`, `max-fields` and `max-string`. Values above the native
field range wrapped before R7 compared them with the allowed defaults. This
violates the positive tightening semantics of
[[SPEC-019-state-rules#CON-1907]] and weakens installation correspondence for
[[SPEC-038-lvar-state-kernel#REQ-3810]].

## Reproduction and evidence

Run `cargo test -p cbcl-parser --test finite_lattices
oversized_state_bounds_do_not_wrap_into_defaults`.

A valid three-element dialect with `(:state-bounds (max-list 4294967360))`
installed: 2^32 + 64 became 64. The pre-fix regression failed with
`max-list=4294967360 wrapped into 64`.

Equivalent inputs 2^32 + 32 and 2^32 + 2048 affect `max-fields` and
`max-string`. The parser's positive-number guard does not exclude these
representable `i64` values. `max-number` already retains its signed `i64`
value and does not use this truncating conversion.

## Required correction

Recognize the exact unsigned field range with checked conversion before any
state-bound semantic action. Reject oversized literals rather than wrapping
or clamping them. Preserve valid input syntax, canonical identities and native
R7 default-tightening checks. Exercise the actual strict dialect parser and
installer, not an independently built native Bounds structure.

## Verified correction

The aggregate Lean build and Batteries environment linter pass, with 1843
allowlisted theorem audits. All six live Rust/Lean oracle suites pass with
`PROPTEST_CASES=512` and `PROPTEST_RNG_SEED=380038`. Selected parser, finite,
state, export and corpus suites pass. Focused proof mutations reject bypassing
the authored bounds gate and corrupting default/positivity predicates.

The strict parser regression covers all three oversized unsigned fields.
Restoring the truncating `max-list` cast makes that regression fail again.
The fix uses checked `u32::try_from` conversions before installation.
