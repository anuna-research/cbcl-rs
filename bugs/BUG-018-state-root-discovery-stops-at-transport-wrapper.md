---
id: BUG-018
title: State root discovery stops at an outer transport wrapper
severity: S2
priority: P1
status: resolved
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-core/src/state.rs
---

# BUG-018: Accepted sealed roots disappear behind transport wrappers

Cast extraction traverses non-role wrappers, but state root discovery checked
only the outermost message's wrapper type. A valid `signed` wrapper around a
sealed `with-roles` root was admitted; admitting its first child then returned
`Pending`, since `Instance::new` could no longer recover that accepted root.
The expanded `progress_uses_pinned_role_root_and_accepts_competing_members`
regression executed and failed at its public admission assertion.

This is inconsistent root discovery, not a grammar extension or a state-dependent
admission policy. Root discovery and progress now share the same root predicate
and wrapper traversal used for the approved identity policy. Cast validation,
protocol checks, and authenticated signer premises still apply.

Separately, migration exposed progress pinning the old simple-message hash even
when causal edges used the new sealed root address. The existing progress
regression executed and returned number zero instead of two. Progress now pins
the actual state address. The deliberate `progress-pins-legacy-simple-root`
mutation must make that executed regression fail.

Acceptance: direct and transport-wrapped sealed roots both support public
admission of competing repeat members and report progress two/count three,
including reversed delivery; native library and integration checks pass;
independent review finds no concrete defect. The root migration and wrapper
identity contract are [[SPEC-038-lvar-state-kernel#ADR-3807]] and
[[SPEC-038-lvar-state-kernel#TEST-3814]]; progress remains governed by
[[SPEC-038-lvar-state-kernel#REQ-3803]].

## Resolution — 2026-11-09

Implemented and independently reviewed under
[[SPEC-038-lvar-state-kernel#TEST-3814]]. Native library and state integration
suites pass, including transport-wrapped root admission and progress. The
explicit migration manifest preserves the immutable historical snapshot and
checks exact original state bytes. Live Lean oracle and progress comparisons
pass. Executed semantic mutants reject cast omission, the wrong root predicate,
stale candidate identity, transport-stopping discovery, legacy progress pinning,
and raw-render whitespace drift. Compiler or disk-space failures were not
counted as mutation rejection; the final isolated gate passed after regenerable
build caches were removed.

This resolves the root identity/discovery implementation defect; authored
condition thresholds and the full v0.4 acceptance audit remain separate work.
