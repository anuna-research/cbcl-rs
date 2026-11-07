# CBCL checkpoint certificates

This crate implements the reusable native checkpoint companion dialect and the
version-2 state-summary profile from [[SPEC-035-cached-state-checkpoints]]. A client
opens a certified cut and admits its tail without replaying covered target history
or downloading the companion thread. Certificates rely on the pinned member/fault
policy; they do not prove global freshness or authorize garbage collection.

## Quick start

```sh
cargo test -p cbcl-parser --test checkpoint_dialect
cargo test -p cbcl-checkpoint
cargo run -p cbcl-checkpoint --example cached_checkpoint
```

The example uses public deterministic test keys and temporary local storage.
Applications supply their own key custody and strict signature verifier.

## Usage

Install the standard definition with
`cbcl_parser::checkpoint_dialect::builtin()`. Its native content identity, rather
than its human label, identifies the dialect. Independently pin a target installation,
target root, companion root/cast and static `Policy`. Use
`Summary::expected_profile_hash_for` with the target clause and pinned protocol, then construct an
immutable `Context::new`; network messages cannot replace that trust configuration.

Maintain an independent `Member` through ordinary signed target-message admission.
Freeze its manifest and summary. Pin the signed companion opener, authorize each
native endorsement through `Member::authorize_endorse_with_opener`, and sign the
opaque capability through `ManagedSigner`. Its generic authoring method refuses
endorsements. The low-level `KeySigner` trait is a trusted host/key-custody boundary,
not an API to expose to untrusted authors.

Any member can assemble and advertise a `Certificate`. Its blob carries the native
bootstrap and original signed endorsements; proposal/publication history is not a
verification prerequisite. `Certificate::verify` establishes the attestation policy.
`Client::from_certificate` additionally recognizes the supported summary profile.
Providers construct `Step` proofs against the precise pre-step root. Clients verify
all signed dependencies and ordinary causal/shape rules before advancing coverage.

For durable returning clients, call `DurableClient::prepare_bounded`, then
`runtime::start_install(...).wait_deadline()`. The prepared handle binds that store's
actual floor, generation and writer instance. Installed views and pending old views
share immutable `Arc` snapshots, so foreground capture does not copy live state. Concurrent admission, evidence, outbox
and retry changes invalidate it. Stalled validation returns cancellation without
installation. An OS commit that exceeds the shared deadline returns an `Uncertain`
handle which retains the writer fence and old view; observe its completion or recover
the durable generation. It is never reported as a rolled-back write. Synchronous
helpers are also available for controlled batch hosts.

Modes are `Off`, `Shadow`, and `Enabled`; applications start in `Off`. Shadow
installation requires `compare_shadow` against an independently admitted native
history and does not change the installed generation. Disabling preserves state,
floor, evidence and outbox. Ordinary full replay is an explicit operation requiring
the signed archive; it is not an unbounded automatic fallback.

## Architecture

- Pure, `no_std` modules compose the existing CBCL kernel/parser: native certificate
  recognition, immutable coverage proofs, incremental summaries, member derivation
  and verified continuation.
- The `std` host owns bounded retrieval, publication scheduling, OS writer locks,
  immutable content-addressed files and atomic generation records.
- Coverage snapshots and evidence archives share persistent structure. A generation
  references one immutable evidence-tree root. Warm installation writes new evidence
  and copied index paths, without reopening the retained prefix's bodies.
- Semantic rows retain selected contributions, rather than complete messages or
  signatures. Original signed bytes remain separately retained, including
  alternative valid signatures.

Version 2 supports all 16 native rule heads. Exists/count/counter use compact
scalars; set-union retains distinct selected values; events retain only identity,
signer and selected value. Replacement-sensitive rules retain live projected
contributions and pending references. Histogram/sum read earlier materialized map
fields. Ordinary non-repeat protocols without progress output retain no historical
position cache.

Repeated protocols resume native R5 verification from scoped causal metadata and
materialized positions, including clauses without a progress field. Resource
counters retain projected cast/resource facts and sparse referenced-identity
presence, then use the same native escrow verifier as full replay. Resource facts
can grow, and resource update/recognition work grows with that evidence. A state
checkpoint is an observation, never spend authorization or resource finality.
Native collective/quorum policies retain their existing unsupported-finality fault
tags. Domains and global all-occupant fan-in remain separate unsupported features.

The binary summary/profile is version 2 and binds the pinned causal protocol.
Version-1 summary bytes are rejected. The exact closed grammar is in
[WIRE.md](WIRE.md), with generated canonical byte vectors under
`test-vectors/checkpoints/v2-wire-vectors.json`. Live output, event output, frontier width,
protocol metadata, resource evidence and provider archives can grow; checkpointing
does not imply constant-size state.

## API reference

```sh
cargo doc -p cbcl-checkpoint --no-deps
cargo check -p cbcl-checkpoint --no-default-features
```

`certificate` defines pinned contexts, native messages, policy and portable bundles.
`coverage` defines presence/absence and insertion proofs. `summary` implements the
render/continuation laws. `member` separates independently reconstructed signing
members from clients opened through certificates. `host` and `runtime` implement
the durable lifecycle and bounded scheduling. `PublicationSchedule` coalesces work;
`publish` persists verified immutable bytes before invoking discovery.

Opening metrics separate decoding, verification/summary recognition, retrieval,
tail admission, floor checks, retention and commit. Byte totals include certificates
and offers with tail/dependency/floor subcategories. Failed fetch allowances are
charged conservatively to the cumulative budget; that charge is not a claim that
all reserved bytes were physically received. Persist-work counters separate new
bodies/index nodes from metadata-only checks of already durable roots.

## Development

```sh
cargo test -p cbcl-checkpoint
cargo clippy -p cbcl-checkpoint --all-targets -- -D warnings
python3 scripts/check-checkpoint-mutations.py
python3 scripts/check-checkpoint-all16.py
```

The suite checks the ordinary core fold and admission monitor, native role/cast
binding, retained evidence, stale/forked floors, malformed binary inputs, cumulative
budgets, write/sync/rename fault injection, writer fencing, shadow comparison and
deadline uncertainty. Scaling distinguishes covered history from live state,
frontier, protocol size and explicit dependency lookups. It does not infer a
constant-space result from a small snapshot.
