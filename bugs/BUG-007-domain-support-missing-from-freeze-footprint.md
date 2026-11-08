---
id: BUG-007
title: Domain dependencies omitted from frozen field support
severity: S2
priority: P0
status: fixed
reported-date: 2026-11-09
assigned-to: SPEC-038 implementer
component: crates/cbcl-core/src/state.rs
---

# BUG-007: Domain support can fall outside a frozen field's cone

The retained contribution set of a domain-filtered field must include the
initializer or sealed roster root that supplies its domain, as well as eligible
writers. Omitting this dependency lets an admitted freeze retract a successful
threshold without exposing a fault. This violates
[[SPEC-038-lvar-state-kernel#REQ-3800]],
[[SPEC-038-lvar-state-kernel#REQ-3802]],
[[SPEC-038-lvar-state-kernel#REQ-3803]] and
[[SPEC-038-lvar-state-kernel#REQ-3806]].

## Reproduction and evidence

Run `cargo test -p cbcl-parser --test freeze_reads
admitted_domain_initializer_outside_freeze_cut_preserves_threshold_or_fault -- --exact`.
The fixture installs a strict parsed dialect whose protocol permits
`(then begin open)`, `(then (any begin open) write)` and `(then write close)`.
Its initial options supply the domain of a counted writer; a threshold requires
one writer, and close freezes that count with fault policy.

An opener and writer both cite the pinned metadata root; close cites the writer.
The actual AdmissionMonitor accepts the entire trace: projection interprets a
reference to that metadata root as begin. The opener therefore lies outside
close's business cone even though its domain admits the writer.

Before the repair, the executable regression reaches its assertion after
installation and monitor acceptance, then fails because reached becomes pending
without a fault. Captured locally in
`/tmp/spec038-admitted-domain-freeze-red.log`. After repair it passes, reporting
fault evidence containing the opener and freezer. The fixture gate accepts only
its fixed full-message corpus; this demonstrates monitor behavior conditional on
authentication, rather than proving cryptographic verification or deployment
address extraction.

A separate context regression,
`domain_roster_root_outside_cut_is_retained_as_freeze_support`, isolates the same
missing dependency for a sealed role roster. That deliberately incomplete graph
is a low-level state fixture, not an admitted trace.

## Root cause and repair

Root-cause category: omitted semantic dependency. The freeze footprint recorded
eligible domain-filtered writers but omitted their domain sources. Requiring
business-opener dominance would reject protocol behavior already permitted by
admission and would not repair the underlying dependency omission.

The repair retains every applicable initializer and roster root in the freeze
footprint, including malformed or currently noncontributing support. Fault-policy
cuts missing such evidence expose the contribution and freezer witnesses;
superseding cuts record the excluded contribution. Domain evaluation itself and
protocol admission remain unchanged.

The Lean model includes the same support branch. The locality proof derives
exact equality of allowed sets and selected writers for healthy fault-policy
cuts, including multiple initializer and roster domains; count thresholds then
survive growth or expose a fault. It does not assume opener dominance.

## Verification and remaining scope

The aggregate Lean build and Batteries environment linter pass. The axiom audit
checks 1541 theorems with only allowlisted axioms. Native freeze and context
suites pass (19 and 14 tests); the admitted regression also checks reverse and
duplicate delivery. All 30 isolated native semantic mutations fail their
executed tests, including separate removal of initializer and roster support.
The focused proof mutation removing domain support from the healthy-cut premise
fails `domain_allowed_cut`. Independent review found no repair, proof or artifact
defect. Verified-by lint passes; the spec vault adds no unresolved link pairs or
syntax/SPL errors.

General wire extraction, native representation correspondence and broader
source-policy composition remain separate SPEC-038 obligations. Fixing this
failure does not claim completion of those obligations.
