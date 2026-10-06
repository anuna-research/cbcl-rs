# Issue 18 independent adversarial review

Date: 2026-10-06. Reviewer: independent Codex agent, identified by its session instructions as GPT-6. The exact runtime model variant is not exposed to this reviewer. The generating model's family/version was not supplied; the coordinator must record it and establish model diversity before describing this record as satisfying the cross-model gate. This is an AI review, not human review or human domain-expert approval.

Scope: [[SPEC-019-state-rules#REQ-1933]], [[SPEC-019-state-rules#REQ-1934]], [[SPEC-019-state-rules#TEST-1951]], [[SPEC-019-state-rules#TEST-1952]], [[SPEC-019-state-rules#TEST-1953]], and [[IMPL-019-signer-register]]. The review started with the specification, implementation/test/documentation diff, and a mandate to find defects. No implementation-author reasoning was supplied.

Result: no blocking implementation defect identified in the reviewed signer amendment. The maintainer should use this review alongside the implementation evidence and the separate human review required by Tier 2.

## Concrete checks

- Signer supersession: `Kernel::current_by_signer` obtains writes through the verb/domain selection, collects `(signer, replaced-address)` pairs, and excludes only matching writes. A replacement from another signer or verb cannot erase the target. All admitted writes supply replacement edges, including writes that have themselves been replaced, so an older value cannot resurrect when its replacement is superseded.
- Selection order: `LatestPerSigner` groups surviving writes before picking the greatest address. A lower-address observed edit therefore wins when it names the previous surviving writes. An unobserved concurrent write remains eligible. `Last` and `LatestPerKey` still select from `acts`, and the keyed `current` implementation is unchanged.
- Domain ownership: `kernel_for` extracts the fold's existing domain setup without changing it, and the binder reuses that kernel for signer targets. Excluded writes neither enter the current set nor supply replacement edges. Signer comparison uses authenticated act metadata, not payload fields.
- Binder concurrency: all own current writes are collected, including losing concurrent candidates; other signers are excluded from the signer rule's contribution. The first signer write creates `Some(empty)` bookkeeping. Supplied `:replaces` remains rejected before binding.
- Shared replacement fields: a verb feeding both keyed and signer rules unions their targets. Keyed rules can legitimately contribute another signer's address; signer selection still ignores that cross-signer edge. Sorting, deduplication and prefix truncation are applied consistently. Truncating intermediate unions is equivalent to truncating the final union: an omitted address already has at least `max-list` smaller distinct addresses that remain present in the final union. No rule-order defect was found.
- Reserved shape: signer writers are included in `replaces_verbs`, compiler shape insertion remains idempotent, and state-shape checking explicitly requires bookkeeping on replacement writers. Existing list/address/duplicate/bounds validation still runs. A verb used only by `Last` does not gain the field.
- Lean correspondence: `currentOwn`, `latestPerSigner`, and `histogramPerSigner` use the new selection; the fold invariance proof now uses `currentOwn_setEq`. The new binder theorems describe an unbounded abstraction with domain-prefiltered input. Their comments and the specification explicitly exclude Rust's finite sorted-prefix policy from the proof claim. Fresh-write currency includes freshness and previously-unnamed-address hypotheses. No new `axiom`, `sorry`, `partial`, or `unsafe` declaration was found in the reviewed state model diff.

## Independently executed verification

```text
cargo test -p cbcl-core --test state_properties signer_
test result: ok. 8 passed; 0 failed

cargo test -p cbcl-parser --test state_exports signer_replaces_shape_is_exported
test result: ok. 1 passed; 0 failed

cargo test -p cbcl-parser --test state_layer signer_writer_requires_replaces_but_last_does_not
test result: ok. 1 passed; 0 failed
```

The review also inspected the canonical signer corpus, JavaScript authoring regression, export tests, dialect documentation, and axiom-audit additions. The full workspace/JavaScript suites and Lean build were reported green by the coordinator; this reviewer does not claim to have independently rerun them or the mutation campaign.

## Limits relevant to acceptance

The bounded policy deliberately does not guarantee one edit eliminates every observed concurrent write when their target union exceeds `max-list`. A surviving higher-address write can still win in that case. This follows the explicit bounded requirement and is not an implementation defect against this amendment. The unbounded Lean supersession theorem must not be presented as proving the bounded Rust binder eliminates all observed writes.

The reviewed diff includes a state-shape export tightening for existing keyed replacement writers as well as signer writers. This agrees with their already-required compiler-owned shape and does not alter their fold or binder selection semantics.

Human review remains separate. This record establishes an independent adversarial session; model-family diversity requires coordinator evidence, not inference from an agent label.
