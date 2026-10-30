---
title: Quorum runtime API
mode: reference
---

# Quorum runtime API

`cbcl_core::quorum` implements the consensus-free bounded-counter safety protocol
specified by [[SPEC-026-rust-quorum-certification]]. Its public types use `alloc`;
optional `serde` supports typed transport and journal serialization. Parsing and
allocation limits belong at the host's wire boundary before constructing these types.

## Context and defaults

`Context::from_instance(&instance, field, instance_validators, &auth)` validates the
selected quorum rule, authenticates genesis, reconstructs its cast, and pins the
canonical dialect, thread, root, opener, resource field and committee. Existing
uncertified history contributes no capacity or balance. The context owns genesis
and dialect data. Certificates from another context cannot be replayed into it.

| Declaration | Resolution |
|---|---|
| No certification clause / `host-gate` | Existing `escrow::issue` host gate |
| `quorum-budget` | Require authenticated instance roster |
| `quorum-budget (validators @v0 @v1 @v2 @v3)` | Pin dialect roster, infer `f=1` |
| Explicit `(faults f)` | Check exact `n=3f+1`; quorum always `2f+1` |

Roster order canonicalizes. Duplicate or malformed members reject. An explicit
instance roster must match an explicit dialect roster. Validators are never inferred
from holders, balances or caller request fields. The single-validator `f=0` profile
is valid mathematically; it tolerates no Byzantine validators.

## Host authentication and persistence

Implement `Authentication` with these independent responsibilities:

- `authenticate_act(act)`: verify the owner's real signature and normal CBCL
  protocol admission, including authenticated sender/wrapper semantics.
- `verify(key, preimage, signature)`: authenticate a vote using the pinned key.

A wrapper named `signed` does not satisfy either responsibility. The core rebuilds
act identity and separately checks context, closed shapes, duplicate parameters,
owner roles, issuer authority, accounts, positive amounts and compiler evidence.

Implement `Journal` per `(context ID, validator key)`. `load` returns the entire
acknowledged log or `None` only for a previously unused identity. `append` atomically
creates that identity when `expected=None`, or appends when the existing event count
matches `Some(sequence)`. A failure must mean no append occurred. The acknowledged
log must survive crashes without truncation, rollback, forks or lost choices. Shared
processes using one validator key must use this same storage namespace and atomic CAS.
Do not initialize the same previously used key against an empty replacement store.

`Replica::initialize` creates once and refuses existing logs. `Replica::recover`
replays all typed events through semantic guards and rechecks received signatures;
it never trusts a deserialized balance or counter. Events contain complete acts and
proofs. Recovery has no clock, timeout unlock, or signing-budget reset. Signature
verification and act admission must remain deterministic for the pinned instance.

Every mutation applies to a tentative state, appends its event, and only then
exposes a signing request. Storage/CAS failure restores the previous state and
returns no signing request. Retrying a durable vote returns the same preimage.
Physical durability is a host obligation, not a property of an in-memory test log.

## Transaction and certificate operations

| API | Meaning |
|---|---|
| `intend(instance, owner, verb, fields, nonce)` | Shared CBCL binder, adding epoch, dependencies and nonce before owner signing |
| `register(act, journal, auth)` | Authenticate and retain a candidate; missing dependencies reject for fetch/retry |
| `prepare_operation(id, journal, auth)` | Enforce local epoch and scaled budget; persist before returning signing bytes |
| `receive(certificate, journal, auth)` | Verify every distinct member signature and complete local prerequisites |
| `prepare_effects(id, journal, auth)` | Require operation QC and no local cancellation fence |
| `prepare_cancel(owner_request, journal, auth)` | Verify owner request, require no prior local effects vote, persist fence |
| `release(id, journal, auth)` | Require own recorded charge plus cancellation QC; retain all evidence |

The caller externally signs the complete message returned by `intend`, then submits
its authenticated `Act`. Caller-supplied `escrow-prev`, `escrow-deps` and
`escrow-nonce` reject. The nonce is a nonempty string of at most 256 bytes, supplied
as the explicit API argument. Reuse it for retries; choose a different nonce for a
new identical payment. Epoch changes also change transaction identity.

`SigningRequest::preimage()` supplies exact bytes to the external signer;
`attach(signature)` creates an untrusted `Vote`. Assemble a `Certificate` with its
kind, payload ID and member votes. Receipt checks actual signatures, context, kind,
payload and distinct-member quorum; constructing the struct confers no authority.
An operation QC is pending capacity. Effects QC is finality for that operation.
Effects and cancellation QCs cannot coexist under the honesty assumption.
Conflicting genuine certificates return an explicit error; they are never resolved
by choosing a hash or arrival order. Treat that error as a violated assumption.

`Context::cancellation_request(owner, id)` supplies separate owner signing bytes.
Cancellation does not introduce a business `extend` message or bypass normal act
signing. No private key or signing algorithm is embedded in the runtime.

## Checkpoints

`seal(epoch, journal, auth)` persists closure before returning the full local
signed-ID set and a seal signing request. Construct `SealReport { epoch, signed,
vote }` after external signing. Released and zero-cost signatures remain present.
Fresh signatures in a sealed epoch reject; cached vote retries remain identical.

`draft_checkpoint(epoch, reports, refunds, credits)` computes cumulative contents
and exact allocation. Refunds need cancellation QCs; credits need effects QCs.
Sign `Context::checkpoint_request(manifest)` as the account owner, then construct a
`Proposal`. `register_proposal` verifies owner authorization, seal quorum, complete
report inclusion, parent/depth, cumulative sets, funding proofs and exact books.

`prepare_checkpoint` requires the validator's own sealed journal to be included
and persists its one-successor choice. Assemble a checkpoint QC and a `Checkpoint`.
`receive_checkpoint` independently verifies the whole proposal and QC.
`install` only follows the local active parent. Replayed old checkpoints cannot
reset the active epoch. `active_epoch` provides the installed local epoch.
Alternate report bundles proving the same manifest share its semantic ID.

The accounting equation for each resource is:

```text
allocation = genesis + cumulative final credits
                     - cumulative held costs
                     + cumulative cancellation-backed refunds
```

There is no consensus recovery path for split successor votes or effects/fence
splits. The protocol guarantees safety under its assumptions, not unconditional
progress or immediate spending of an entire displayed balance.

## Queries and limits

`finalized_view` returns known-final IDs, pending operation IDs, rights, optional
headroom, value and an evidence digest. `value()` renders `status: finalized-view`
and `completeness: unknown`. This is a dependency-closed local certificate view;
it is neither a complete latest balance nor guaranteed immediately signable capacity.
The digest commits the context and final operation set, not a quorum-signed balance.
`fold_instance` overlays this selected field on the normal state fold. Generic
stateless parser/WASM/FFI folds remain fail closed for quorum counters.

`operation_act`, `certificate` and `checkpoint` return retained evidence for host
fetch/relay protocols. They never synthesize signatures or completeness claims.

`Limits::default()` admits at most 4096 candidates, 1024 proposals and checkpoints
each, 65536 journal events, 1 MiB per operation object, and 8192 bytes per signature.
The typed message traversal also enforces a depth ceiling of 64 before recursive
canonicalization. Cardinalities and known-ID checks bound certificate/report inputs.
The host can choose stricter limits and must bound decoding before allocating inputs.
Hitting a limit refuses new work and retains safety evidence. It does not garbage
collect histories, fences, signatures or choices. Limit changes on recovery must
still admit the full existing log.

The executable example is `crates/cbcl-parser/tests/quorum_runtime.rs`. It uses
explicit test-only authentication and in-memory CAS journals. Production signing,
transport, nonforking durable journal providers and complete-history read protocols
remain host integrations. Rust/Lean correspondence is tested and reviewed, not
formally extracted or proved.

## Collective pool API

`CounterRule::ownership` defaults to `Ownership::Account`. Collective rules use
`Ownership::Collective`, `(initial open :available)` and no transfer mapping.
`CounterRule::transfer` is now optional: account rules require `Some(tuple)`, while
collective rules require `None`. Existing tuple JSON is compatible with `Some`;
missing serialized ownership defaults to account.

`Context::ownership()` reports the mode. `Context::pool()` returns the reserved
`COLLECTIVE_POOL` resource scope in collective mode. Genesis rejects a cast key
matching that scope. Actor authorization always uses real authenticated signers
and the pinned cast. `Replica::intend` reconstructs public Instance caches before
using the shared binder.

`root_epoch(actor)` and `active_epoch(actor)` resolve every collective actor to the
same pool epoch. They also accept the explicit resource scope for read access.
The resource scope cannot sign transactions, cancellation requests or checkpoints.

`checkpoint_request_by(manifest, actor)` returns signing bytes for an admitted
operation actor. Use this method for collective checkpoints; the older
`checkpoint_request(manifest)` remains valid for account ownership. Incoming
proposals independently recheck the actual authorizing actor. Cancellation continues
to require the original operation signer. Neither role authorization nor the
pool's balance can replace that cancellation signature.

`FinalizedView` exposes its ownership mode. Rust `rights` and optional `headroom`
maps contain one pool entry for collective rules. `value()` renders scalar resources
and `ownership: collective`. Final-set digests and unknown completeness retain their
existing meaning. Collective checkpoint accounting and journals use the same pool
scope across all actors. No multi-parent merge, consensus fallback or unconditional
progress is implied. See [[SPEC-027-collective-bounded-counters]].

## Explicit collective Lean protocol

[[SPEC-028-collective-actor-refinement]] formalizes signed request admission,
concrete cast/role checks, per-validator receipts and shared-pool execution in
`LeanCbcl/ConsensusFree/CollectiveProtocol.lean`. Cancellation quorum provenance
names the original transaction actor; checkpoint quorum provenance names an
eligible authenticated proposer. Receipt/rejection steps erase to stuttering in
the existing resource protocol. General proofs cover finite and infinite safety,
funded refinement, declared floor/ceiling, retained successor choices and safe release.

Run `lake env lean --run CollectiveActorAudit.lean` from `lean-cbcl` for the
kernel-checked traces and axiom audit. `CollectiveActorAdversarialReview.lean`
contains independently authored checks. Ideal signatures and fixed identifiers
binding complete immutable payloads are assumptions. Parser/crypto correctness,
physical durability and formal Rust correspondence remain outside this proof.
Abstract event-log replay is distinct from the Rust journal serialization, and
this system model does not establish complete/latest client balance reads.

## Multi-parent collective protocol

`Context::from_instance_multi_parent(&instance, field, roster, &auth)` selects
[[SPEC-030-rust-multi-parent-refinement]]. It requires collective ownership and uses
a distinct context domain. Existing `from_instance` keeps the single-parent
protocol. There is no journal migration: signatures, roots and logs from the other
mode cannot be mixed. `Context::handoff()` reports the selected mode. Dialect
syntax and external transaction signing stay the same.

Multi-parent mode replaces seals, one-successor endorsements and checkpoint QCs
with authenticated version metadata and independent local adoption:

```text
        A --\
       /     \
root          M --> N
       \     /
        B --/
```

| API | Meaning |
|---|---|
| `version_snapshot()` | Complete local signed history, visited/known versions and retained fences/releases |
| `draft_version(parents, held, refunds, credits)` | Union parent sets and compute exact genesis-based books |
| `Context::version_request(manifest, actor)` | Version authorization bytes for an eligible actual actor |
| `receive_version(DagVersion, journal, auth)` | Independently verify metadata, actor signature, parents, ranks, sets and funding proofs |
| `adopt_version(id, journal, auth)` | Require active version among direct parents and every historical signature ID held |
| `version(id)` | Fetch retained validated metadata for relay |

A host gathers candidate IDs/history through its transport, drafts a covering
manifest, externally signs its authorization request, relays the version, and lets
each validator adopt independently. No version/checkpoint vote is needed. Omitted
IDs cause an adopter to refuse; a proposal cannot reset its history. Released and
zero-cost signatures remain obligatory. Refunds require real cancellation QCs and
credits require effects QCs. Parent balances are never added. Proposals that reserve
more than genesis plus credits require cancellation-backed refunds before adoption
can succeed. No consensus fallback or unconditional progress guarantee is supplied.

`VersionManifest::rank` exceeds every parent rank and every held operation's source
rank. Drafting computes the smallest such rank; callers can choose a larger rank
before reauthorizing a manifest. Siblings can have equal rank. The label is not a
global transaction order. The semantic ID binds parent IDs, rank, sets, allocation
and context; changing any field requires a new actor authorization.

All transitions use the same tentative-apply/atomic-append/expose discipline as
operation signing. Recovery rechecks DAG guards and rejects wrong-mode legacy
events. Metadata receipt never activates a version, nor does it imply another
validator has received its proofs. Effects preparation still requires the locally
received operation QC; a version importing credits requires locally verified
finality. `finalized_view` retains its local, completeness-unknown meaning.
Limits also bound DAG versions/parents and cumulative transaction sets. Overflow
rejects; no evidence is dropped to regain capacity. Cached signing/adoption retries
return existing evidence or stutter.

The Lean numeric model is [[SPEC-029-multi-parent-counter-model]].
`MultiParentRustOracle.lean` proves its Rust API adapter refines abstract steps.
The adapter makes source-metadata registration, own-charge release and idempotent
retries explicit. The shared fixture synchronizes verified metadata/certificates;
separate Rust tests cover delayed delivery. `quorum_runtime/multi_parent.rs` compares
real runtime admission and projected state and recovers the journal after every
shared step. Regenerate/check with:

```sh
python3 proofs/validator-budget/check_rust_multi_parent.py
cargo test -p cbcl-parser --test quorum_runtime multi_parent
python3 proofs/validator-budget/check_rust_multi_parent_mutations.py
```

This is tested transition correspondence with the proved Lean reference, not a
universal Rust source-equivalence proof. Machine integer/catalogue limits reject
additional inputs. Packet codecs, cryptography and physical journal durability
remain host assumptions. The new mode does not implement account transfers or
prove unbounded fresh-ID refinement.
