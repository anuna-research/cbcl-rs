# Cached checkpoint implementation evidence

This directory records local acceptance of
[SPEC-035-cached-state-checkpoints](../../specs/SPEC-035-cached-state-checkpoints.md)
on upstream main `3186cea`. The separate upstream register specification also uses
number 035; references here identify the checkpoint specification by its full stem.
The implementation is opt-in and defaults to `Off`.

The reusable native dialect lives in
[checkpoint.cbcl](../../dialects/checkpoint.cbcl). The implementation and runnable
example are described in the [crate guide](../../crates/cbcl-checkpoint/README.md).
The [executable plan](../../plans/IMPL-027-cached-checkpoints.spl) records its task
and acceptance dependencies in Elephant theory `spec-035-cached-checkpoints`.

## Current all-head Profile v2

The current implementation supports all 16 native rule heads, including projected
Events, ordered Histogram/Sum sources, native progress-position continuation and
resource observations. It remains opt-in (`Off` by default). Domains and global
all-occupant fan-in are separate unsupported features.

- `all16-workspace.log`: 1,739 workspace tests passed, zero failures; 36 ignored
  tests include explicitly run external-tool/depth suites.
- `all16-clippy.log`, `all16-format.log`, `all16-wasm-no-std.log`: strict workspace
  Clippy, formatting and the no-std WASM build passed.
- `all16-lean-checks.json`: six trust-zero model/test checks; 41 named theorems
  depend only on Lean's three foundational axioms; all four semantic proof
  mutations are rejected inside proofs. `all16-lean-build.log`,
  `all16-lean-lint.log` and `all16-axioms.log` record the complete build, linter
  and 423-theorem repository axiom audit.
- `all16-parity-evidence.json`: 231 prefix/cut records compare all 16 fields on
  both the Lean snapshot and independent native-expression full-fold paths with
  Rust (7,392 comparisons). Three controls compile/run successfully and then
  diverge on selected event value, causal parent and resource allocation.
  `test-vectors/checkpoints/all16-parity.json` contains input-only typed fixtures.
- `all16-resource-policy-parity.json`: 20 prefix/cut records compare the two
  legacy collective/quorum fault policies using actually installed native
  configurations, Rust full-fold, resumed summary and independent Lean policy
  ports. This checks those constant fault modes, not general resource finality.
- `all16-runtime-mutations.json`: all 17 compiled guards are caught; the isolated
  snapshot restores exactly and matches current source. `all16-summary-mutations.json`
  records eight additional compiled summary mutants caught by their tests.
- `all16-events-projection.json`: 2,000 authenticated signed bodies total
  10,296,890 bytes; the equivalent selected event summary is 184,942 bytes
  (55.68× smaller). This projection fixture is not a protocol-admission or
  end-to-end latency benchmark. Certificate, tail, frontier, proofs and retained
  evidence are excluded from these byte totals.
- `test-vectors/checkpoints/v2-wire-vectors.json`: canonical version-2 records
  cover all 16 heads, all 11 row tags and nested progress/resource formats.
  The exact grammar is [WIRE.md](../../crates/cbcl-checkpoint/WIRE.md).
- `all16-proof-review.json`, `all16-progress-review.json`,
  `all16-resource-review.json` and `all16-parity-review.json`: bounded local
  same-model reviews disclose authorship, dependency overlap and checked scope.
  They are not human or independent security approval.

The all-head Lean theorem uses the existing native typed kernel. Wire extraction,
clock/signer interpretation, protocol evidence and the resource classifier remain
explicit ports. Resource transport is proved for the same fixed classifier on
both sides; the generic escrow classifier itself is not re-proved or extracted.
The bounded 7,392-comparison corpus uses a recognized single-verb repeat chain
(opener edge mapped to begin) and a separately implemented bootstrap-account
classifier. It does not establish general native classifier/admission refinement.
Native resource prefix/fault/mode tests and actual installed-dialect certificate,
repeat-tail and durable-recovery tests supply additional runtime checks.

Reference histories contain accepted identities once. Raw conflicting duplicate
attempts retain native diagnostics; they are not alternate accepted-store histories.
Native full-fold progress now indexes both native/state address spellings, and the
shared escrow projection normalizes native opener/previous/dependency links to
state-wire addresses. Canonical resource identity commitments equate native AST
aliases, so independently selected equivalent representatives cannot split hashes.

Events grow with output. Protocol metadata and resource facts can grow too;
resource apply/recognition reuses the native graph verifier and scales with that
fact graph. Ordinary nonrepeat drawings without progress output retain no global
position cache. Provider signed archives and durable evidence remain retained.
No read-compaction result here authorizes garbage collection or resource issuance.

## Evidence versions

The original reports below describe the seven-head v1 implementation and its
v0.4 Lean proof. They are historical evidence, not current-source all-16 results.
The v2 extension changes summary bytes, profiles, projected rows and continuation
metadata. Its checks and proof evidence are recorded separately as `all16-*`.

## Evidence

- `checks.json`: commands, outcomes, source identity and verification logs.
- `native-scaling.json`: full native 600/6,000/60,000-message opening and 32-message
  publication measurements, raw output, launch source hashes and timing boundaries.
- `coverage-scaling.json`: persistent coverage index work, storage and independent
  sparse-tree vectors.
- `summary-scaling.json`: current kernel fold/continuation oracle, fixed live-state
  scaling and focused summary mutations. Its historical spec version records the
  worker's starting document; the implementation targets the amended specification.
- `mutations.json`: isolated compiled guard mutations; compilation errors, zero or
  incorrect selected tests, and timeouts never count as detected mutants.
- `implementation-review.json`: independent local agent findings, fixes and named
  regression tests. This is same-model review, not independent security approval.

The original v1 final run passed **1,721 workspace tests**, strict workspace Clippy, formatting,
and the no-std WASM check. All **17 compiled guard mutants** were detected by their
selected tests. Native complete-open median thread CPU was **7.35 / 7.17 / 10.83 ms**
at 600 / 6,000 / 60,000 messages (largest/smallest **1.47×**). Median wall times,
including durable commit, were **47.00 / 48.41 / 55.01 ms**. Certificate and offer
sizes stayed **4,901 + 100,708 bytes**. The source hashes in that native report
identify the historical v1 implementation, and warm persistence encoded only the three new
bodies. The complete timing and prior-client boundaries below qualify these results.

## Traceability

| Specification tests | Implementation evidence |
|---|---|
| TEST-3500 | Immutable installed context; native identity, role/cast, language, thread and signed payload checks in certificate/member/lifecycle tests |
| TEST-3501 | `older_known_cut_derives_independently_unknown_and_tampered_cuts_decline`, imported-client provenance and capability tests |
| TEST-3502 | Native certificate threshold, duplicate signer, forged signature, scope and summary lifecycle tests |
| TEST-3503 | Summary tests compare every supported rule with the existing core fold across prefixes, permutations, suppression, duplicate and HLC replacement cases |
| TEST-3504 | Member continuation tests compare actual native admission; missing, malformed and wrong-position footprints never mutate state |
| TEST-3505 | Concurrent floor tests and cold fallback with authenticated tail; positive final-root proof required for every captured floor head |
| TEST-3506 | Original/alternative signed bytes retained without refolding; persistent archive tests and durable recovery |
| TEST-3507 | Corruption, wrong requested content hash, symlink/special-file handling, cumulative failed-fetch budgets and bounded validation |
| TEST-3508 | Write/sync/rename/directory-sync fault matrix; concurrent accepted-edit, evidence, outbox and retry mutations invalidate prepared handles |
| TEST-3509 | Incomparable independently certified branches and native merged continuation; static policy permits overlapping endorsers |
| TEST-3510 | Entire unsupported profiles refuse installation; generic unknown-profile attestations do not expose state |
| TEST-3511 | Immutable cache content addressing, store-before-advertise, failed publication scheduling and directory durability tests |
| TEST-3512 | `caller_target_coverage_is_proved_explicitly_and_never_promoted_from_hints` |
| TEST-3513 | Off/Shadow/Enabled tests; independent shadow replay; disable preserves state; unavailable replay archive reports missing identities |
| TEST-3514 | Combined native depth rig, actual member archive counters, persistence counters and compiled prefix-scan negative control |
| TEST-3515 | Three independently maintained members append 32 acts, freeze, authorize native endorsements and publish; native replay oracle runs outside timing |
| TEST-3516 | Fixed-seed byte corpus and structured truncation/length/tag/splice/roundtrip tests of all four closed codecs; stalled fetch/crypto and uncertain commit tests |
| TEST-3517 | Built-in dialect tests plus same companion serving distinct targets; capability, scope, thread and quorum mutants |
| TEST-3519 | Lean invariant/continuation proofs, trust-zero axiom audit, semantic proof mutations, Rust/Lean parity corpus and independent reviews |
| TEST-3518 | Foreign-store equal-generation substitution, archive link/directory faults, exact complete-frame generation boundary, owned bounded runtime and writer fencing |

OBS-3500 uses structured opening events and `OpenMetrics`, including actual signature
checks, byte categories, proof paths and phase timings. OBS-3501 uses publication
scheduler/cache events, `MemberWork` and `PersistWork`; the depth rig records their
actual counts. OBS-3502 uses store floor/durable/commit/recovery/conflict events;
a finite-trace test checks matching instance/generation ordering. Provider error
payloads are redacted to closed diagnostic codes.

## Measurement limits

The native depth rig holds one installed dialect/context, eight frontier heads and
live output fixed. Its 60,000 ticks are accepted signed messages, not 60,000 state
edits: only the opener contributes state. Two signed tail messages and their finite
parent openings are verified at each scale. The prior client has a certified floor
and target-root evidence; this does not time creation or recovery of a complete
60,000-body on-disk archive. Separate persistent-archive tests exercise retained
subtrees and verify that unchanged roots encode no historical bodies. The summary
rig measures actual state edits against the native core fold separately.

Publication has one sample per scale and includes three maintained members, 32 new
admissions, summary/coverage updates, freeze, independent endorsement authorization,
certificate verification and durable immutable storage before advertisement. Initial
history admission, dialect installation, proof preparation and the full replay
oracle are outside opening timing and are reported as such. Rendering is measured
separately. These measurements establish the provisional local profile target;
they do not ratify deployment cadence or browser/platform latency.

This is read compaction. Signed evidence and coverage/provider indexes can grow;
there is no garbage-collection authorization or constant-storage guarantee.
The original adapter excluded aggregates, resource counters, progress and repeat
positions. Version 2 adds those heads and projected Events; domains and global
fan-in remain separate unsupported features. Additional profiles,
platform storage adapters, roster transitions, deployment policy and independent
security/domain review remain explicit follow-up work.


## Lean continuation proof

`CBCL.CheckpointKernel.render_advance_checkpoint` proves the continuation law for
arbitrary finite compositions of the **seven enabled checkpoint rule heads**.
The full native kernel has 16 heads; this proof does not make the other nine
checkpointable. The checker compares the proved constructors with the actual
Rust whitelist and separately records the native inventory. Upstream main was
fetched and verified equal to the working baseline `3186cea` during this work.

The statement is exact equality of semantic field values:

```text
render(advance(checkpoint(fields, history), tail))
  = fullFold(fields, history ++ tail)
```

The reference `fullFold` deduplicates accepted identities and invokes the existing
native kernel evaluator. `native_compile_clause` connects supported declarations
to whole native clauses; `render_advance_native_clause` shows the native evaluator
directly in the conclusion. Sets and maps are extensional semantic observations,
not claims about JSON byte order or serialized snapshot hashes.

The row invariant records exactly the surviving writers and the scoped replacement
references whose targets remain unseen. Fresh-step preservation and covered no-ops
compose by induction over an arbitrary tail. Initial rows retain at most two
opener witnesses; plain LWW retains one eligible winner. Keyed and signer LWW rows
retain all unreplaced candidates so deleting a winner can reveal an older one.
The computational snapshot contains finite declared rows and identity-only
coverage; the history appears only in reference evaluation and ghost invariants.

The checked proof is in `lean-cbcl/LeanCbcl/CheckpointSummary.lean`,
`CheckpointCompact.lean`, `CheckpointRender.lean` and `CheckpointKernel.lean`.
The ordinary Lean library imports `CheckpointKernelTests.lean`, including hostile
closed examples. Verification artifacts are:

- `lean-proof-checks.json`: Lean 4.27.0, trust-zero source checks, exact theorem
  statement, runtime/proved rule inventory agreement, transitive axiom audit and
  four deliberately broken updates rejected inside semantic theorem proofs.
- `lean-review.json`: independent agent review of proof meaning, premises,
  sufficient-state representation and connection to native evaluation.
- `lean-parity-review.json`: independent review and rerun of the correspondence
  oracle, including rejection of altered live/pending/value outputs.
- `../../test-vectors/checkpoints/rust-lean-parity-evidence.json`: 1,330
  rule/prefix/cut observations over the actual Rust summary and Lean full snapshot,
  with signed native-ID ranks and HLC/signer ordering evidence. Rust round-trips
  checkpoint bytes at each selected cut. The corpus and exact stdout are retained
  next to that report.

The dedicated theorem audit reports only `propext`, `Classical.choice` and
`Quot.sound`; there are no custom axioms or incomplete proof terms. Existing
repository-wide axiom checks pass separately with their standing allowlist.
The proof is static and adds no per-object proof-generation or verification work.

Rust execution is **not** universally proved or extracted from Lean. The bounded
corpus checks ASCII string payloads/scopes; its immutable per-act clock table is a
recognized-input port. It compares Initial witness cardinality and rendered value,
not which two witnesses are retained: Rust chooses the least two identities, while
the model permits any distinct pair. Synthetic self-replacement is model-only
because native content identities commit their replacement references. Parsing,
normalization, canonical encoding, signatures, admission, authenticated coverage,
certificate fault assumptions, durability and additional profiles remain separate
boundaries. `resume_valid_snapshot` requires the truthful invariant of an imported
snapshot; a signature alone does not supply it.

Reproduce from the repository root:

```sh
(cd lean-cbcl && lake build LeanCbcl && lake exe runLinter LeanCbcl)
python3 scripts/check-checkpoint-lean.py
scripts/check-axioms.sh
CHECKPOINT_PARITY_OUT="$PWD/test-vectors/checkpoints/rust-lean-parity.json" \
  CARGO_PROFILE_DEV_DEBUG=0 CARGO_INCREMENTAL=0 \
  cargo test -p cbcl-checkpoint --test lean_checkpoint_parity -- --ignored --nocapture
```

The v0.3 runtime/performance reports above predate these added proof and
correspondence files. Production checkpoint code is unchanged by the formalization;
proof and parity evidence are recorded independently rather than relabeling an old
benchmark as a new run.
