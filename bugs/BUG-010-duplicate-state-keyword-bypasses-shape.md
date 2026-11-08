---
id: BUG-010
title: Duplicate state keywords separate shape validation from evaluated values
severity: S2
priority: P1
status: fixed
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-core/src/r7.rs
---

# BUG-010: Shape checks the first value while state evaluates the last

The native shape recognizer scans the first matching keyword. Native
`state::keyword_fields` inserts all keyword pairs into a map, retaining the last
value. R7's closed-field scan rejected positional/unknown fields but allowed
repeated data keywords, so these two accepted-message interpretations could
contradict one another.

This violates the stable nonnegative sum premise of
[[SPEC-038-lvar-state-kernel#REQ-3802]] and
[[SPEC-038-lvar-state-kernel#ADR-3805]], and prevents deriving faithful numeric
extraction for [[SPEC-038-lvar-state-kernel#TEST-3806]].

## Reproduction

The actual strict parser and public `state_exports::admit` accept a mint with
`:amount 10 :amount -1` under `(require :amount nonnegative)`. The shape sees
10, but the act's state field is -1. The executable regression is
`duplicate_amount_cannot_hide_a_negative_state_contribution` in
`crates/cbcl-parser/tests/threshold_reads.rs`.

Run `cargo test -p cbcl-parser --test threshold_reads
 duplicate_amount_cannot_hide_a_negative_state_contribution -- --exact`.

Before correction it fails with `ambiguous amount admitted: Accepted`.
This is an observed native admission mismatch, not a failed proof alone.
With an already accepted positive mint of 10, that admitted negative writer
changes `funded` from reached to pending in the native fold. The regression
checks both outputs and accepts the ordinary positive writer as a control.

Raw low-level folding remains total on unadmitted histories; the fix belongs at
the state-shape admission boundary, before a conflicting value is interpreted.

## Required correction

Reject duplicate nonrouting data keywords on state-bearing verbs during R7's
closed-field recognition. Preserve unique-key messages and the low-level
last-value behavior outside the admitted domain. Test admission of the ambiguous
negative contribution, duplicate equal/positive values and unrelated valid
fields. Keep the existing first-keyword shape semantics explicit, and derive
numeric extraction only under a recognized unambiguous parameter grammar.

## Verified correction

R7 now tracks nonrouting data keys during closed-field recognition and rejects
repetitions before interpreting their values. The full threshold-read suite,
selected parser/state/export/corpus/finite tests and all core unit tests pass.
The isolated `duplicate-state-keyword-accepted` mutation restores admission of
the ambiguous negative contribution and fails the named regression assertion.
This repairs the observed native mismatch. General numeric extraction and
routing-key semantics remain separate proof boundaries.
