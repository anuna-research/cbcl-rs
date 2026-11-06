# Register simplification verification

Implements [[SPEC-035-register-semantics#ADR-3503]] through
[[IMPL-025-register-simplification]]. Parent: `8277c4c` on
`draft/state-register-semantics`, PR #20. Date: 2026-11-06.
Steward: Codex `/root`.

## Result

The installed surface has 16 heads. The four primary hash selectors (`last`,
`latest-per-signer`, `latest-per-key`, `register-per-key`) are removed from Rust
Rule variants, S-expression acceptance, JSON authoring, description and JS helpers.
They fail closed, with no aliases. The single LWW family orders by HLC, signer,
then content address as the final exact tie-break. Clock fields remain explicit
host/caller data. Missing or malformed clocks cannot trigger hash-primary fallback.

`initial` is restricted at installation to the unique protocol opener verb.
It reads raw, address-deduplicated candidates before field projection. Missing or
ambiguous candidates yield Absent, including when only one carries the data field.
Repeated receipt of one opener retains the value. Domains use the same initializer.
This does not resolve conflicting bodies claiming the same content address; typed
proof/runtime correspondence retains address consistency as an input boundary.

The Lean surface removes the four retired constructors and introduces `initial`.
`sole_some`, `sole_correct`, `sole_complete`, and `sole_setEq` independently prove
exact singleton recognition, absence on ambiguity, and order/duplicate invariance.
`initialValues_setEq` and the revised domain lemmas no longer need address-uniqueness
premises. Whole-clause correctness and conditional SEC compose this initializer.
Historical address-selector component lemmas are not current elaboration cases.
Resource-verifier classification/finality and Rust equivalence remain separate.

## Migration and compatibility

SPEC-019 and the corpus advance to 4.0.0; the JSON authoring envelope stays at 3.
Canonical form remains 5. New initializer heads and changed definitions receive
new identities; unchanged surviving definitions retain encoding. No legacy runtime
is included. Pin older signed histories to their old runtime, or explicitly migrate
into a new definition/instance. Old names are not silently reinterpreted.

Fixtures now declare and carry clock evidence explicitly. Changed message hashes
and predecessor/replacement references were re-authored together. The one-off
ignored fixture-authoring test recalculates dependencies until stable and refuses
cyclic fixture references. Expected observations were then generated explicitly
through STATE_CORPUS_WRITE and checked again without that flag. These authored
expectations are conformance evidence, not an independent proof of Rust correctness.
The hash-priority property oracle now compares signer/address only because its
fixture HLCs are deliberately equal; dedicated HLC tests cover different clocks.

`latest-per-key` migrations to `lww-map` intentionally add the keyed replacement
contract. Migrated writers carry explicit replacement bookkeeping and clocks;
these are new definitions, not an assertion of unchanged old semantics.

## Verification

Machine summaries and source hashes: `checks.json`. Full falsification diagnostics:
`hlc-mutations.json`, `kernel-mutations.json`, `sec-mutations.json`.

- Core/parser tests and forward/reverse/duplicate corpus, including binder/exports.
- Workspace and no-default-features checks; FFI and Erlang pure binding tests.
  Erlang VM/term integration tests keep their existing ignored status.
- Rebuilt WASM; TypeScript checks; full JS suite, then targeted JS rerun against the
  final rebuilt module. No published browser/package deployment is claimed.
- Lean build, linter and central axiom audit. New initializer results use standard
  axioms only, with no sorry or custom axioms.
- Six HLC/runtime/model mutants, eleven kernel mutants and four SEC mutants.
  A runtime mutation restoring hash arbitration for ambiguous initializers and a
  Lean mutation selecting a candidate from ambiguity both fail their respective
  tests/proofs. Mutation Cargo caches are isolated from the normal build cache.
- Diff/format checks and specification lint; repository checks retain pre-existing
  dead links/older SPL errors. New links and changed numeric anchors are checked.

Earlier version-3 evidence under `proofs/register-semantics/`, `proofs/state-kernel/`
and `proofs/state-kernel-sec/` remains historical and is superseded for current
surface validation by this record. The result still does not establish Byzantine
clock honesty, resource authorization/finalization, or universal Rust correspondence.

## Independent review

Reviewer `/root/whole_kernel_spec_review` inspected runtime, initializer/domain
proofs and public-surface removal. It required candidate counting before payload
projection, distinction between opener verb/history uniqueness, raw initializer
evidence, explicit semantic migration, and no implicit legacy interpreter.
It found two stale FFI/Erlang fixtures and generator coverage strings; those were
migrated and their binding tests passed. It also requested current diagnostics and
oracle comments. Read-only re-review found no remaining blockers.

Reviewer `/root/hlc_orientation_check` initially identified missing initializer
edge behavior, alternative names, clock trust, stored-history migration, and ordering
direction. The Orientation now states each explicitly, including greatest-tuple
selection. It has reading paths and linked decision/requirement anchors. Reviews
are independent tool sessions under one steward, not separate cryptographic peers.

Elephant theory `register-simplification`:
`12384e0e90dc1e1b07259538955ed43ab452ec243a6a9c85b69c7fb1f4c02d51`.
The local store is ephemeral; this plan/evidence preserves the durable result.
