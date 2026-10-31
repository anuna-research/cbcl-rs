---
title: Quorum runtime API
mode: reference
---

# Quorum runtime API

`cbcl_core::quorum` implements the consensus-free bounded-counter safety protocol
specified by [[SPEC-031-unified-quorum-dag]]. Its public types use `alloc`;
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
log must survive crashes without truncation, rollback, forks or lost history. Shared
processes using one validator key must use this same storage namespace and atomic CAS.
Do not initialize the same previously used key against an empty replacement store.

`Replica::initialize` creates once and refuses existing logs. `Replica::recover`
replays all typed events through semantic guards and rechecks received signatures;
it never trusts a deserialized balance or counter. Events contain complete acts and
proofs. Recovery has no clock, timeout unlock, or signing-budget reset. Signature
verification and act admission must remain deterministic for the pinned instance.

Every mutation is validated into an owned local update, then its original event
is appended atomically before that update is applied or a signing request exposed.
Storage/CAS failure leaves the previous state untouched and returns no request. Retrying a durable vote returns the same preimage.
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

## DAG versions

`(certification quorum-budget ...)` always selects consensus-free multi-parent DAG
adoption. `Context::from_instance` derives the runtime from that declaration. The
host supplies cryptography, transport and durable storage, not a handoff protocol.
There is no handoff option, legacy checkpoint API or old-log migration.

```text
        A --\
       /     \
root          M --> N
       \     /
        B --/
```

| API | Meaning |
|---|---|
| `version_snapshot(account)` | This scope's active/visited/known versions and complete own-origin journals |
| `draft_version(parents, held, refunds, credits)` | Derive scope from parents, union cumulative sets and recompute exact books |
| `Context::version_request(manifest, actor)` | Version authorization bytes for the actual eligible actor |
| `receive_version(DagVersion, journal, auth)` | Verify actor, parents, rank, inherited sets, exact books and real credit/refund QCs |
| `adopt_version(id, journal, auth)` | Require current scope's active version among parents and its full signature history held |
| `version(id)` | Fetch retained verified metadata for relay |

An account version is authorized by that account's actor. A collective version is
authorized by an eligible operation actor, never by the pool identity. A host gathers
candidate histories, drafts a covering manifest, externally signs its authorization
request and relays the version. Each validator adopts independently. Receipt makes
metadata known without activating it. No version/checkpoint quorum is needed.

The target must include every historical signature from its resource scope,
including released and zero-cost IDs. Signatures from other accounts do not become
this account's debit obligations. Parents and held operations must share the target
scope; verified incoming transfer credits can originate in another account.
Changing the actor within a collective pool does not change the scope or budget.
Adoption preserves all machine evidence, including other accounts' histories.

The accounting equation is independently checked for rights and headroom:

```text
allocation = genesis + unique cumulative final credits
                     - unique cumulative held costs
                     + unique cancellation-backed refunds
```

Parent allowances are never added. Over-reserved branches need refunds or adequate
verified credits before they can produce a funded join. Cancellation continues to
require the original transaction actor. Missing history blocks an adopter; there is
no timeout unlock, consensus fallback or unconditional progress guarantee.

`VersionManifest::rank` exceeds every parent rank and every held operation's source
rank. Drafting computes the smallest such label; callers can choose a larger rank
before reauthorizing. Siblings can share rank. This is not a global transaction
order. The version ID binds scope, context, parents, rank, sets and allocation.

Versions use the same prepared update, atomic append and guarded recovery as votes.
Recovery recognizes only current typed events; removed legacy event/vote variants
reject during decoding. Cached signing and same-active-version adoption retries
stutter. Old version receipt never resets the active version.

## Queries and limits

`finalized_view` returns known-final IDs, pending operation IDs, rights, optional
headroom, value and an evidence digest. `value()` renders `status: finalized-view`
and `completeness: unknown`. This is a dependency-closed local certificate view;
it is neither a complete latest balance nor guaranteed immediately signable capacity.
The digest commits the context and final operation set, not a quorum-signed balance.
`fold_instance` overlays this selected field on the normal state fold. Generic
stateless parser/WASM/FFI folds remain fail closed for quorum counters.

`operation_act`, `certificate` and `version` return retained evidence for host
fetch/relay protocols. They never synthesize signatures or completeness claims.

`Limits::default()` admits at most 4096 candidates, 1024 DAG versions, 65536 journal events, 1 MiB per operation object, and 8192 bytes per signature.
The typed message traversal also enforces a depth ceiling of 64 before recursive
canonicalization. Cardinalities and known-ID checks bound certificate/report inputs.
The host can choose stricter limits and must bound decoding before allocating inputs.
Hitting a limit refuses new work and retains safety evidence. It does not garbage
collect histories, fences, signatures or visited versions. Limit changes on recovery must
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
The resource scope cannot sign transactions, cancellation requests or versions.

`version_request(manifest, actor)` returns signing bytes for an eligible actual
actor. Incoming versions independently recheck authorization. Cancellation always
requires the original transaction signer; a shared balance cannot replace that
signature. `version_snapshot(actor)` resolves the actor to the same pool scope.

`FinalizedView` exposes its ownership mode. Rust `rights` and optional `headroom`
maps contain one pool entry for collective rules. `value()` renders scalar resources
and `ownership: collective`. Final-set digests and unknown completeness retain their
existing meaning. Collective DAG accounting and journals use the same pool scope
across all actors. See [[SPEC-031-unified-quorum-dag]].

## Proof and execution scope

[[SPEC-029-multi-parent-counter-model]] proves the collective numeric DAG protocol.
`MultiParentRustOracle.lean` proves its API adapter generates valid abstract runs.
The adapter names source-metadata registration, own-charge release and durable
retry stuttering. Shared fixtures synchronize verified metadata/certificates;
separate Rust tests cover delayed local receipt. Tests compare real runtime
admission/projected state and recover journals after every shared command.

Account DAG behavior additionally has transfer, headroom, scope isolation, branch
join, late-certificate and recovery tests. It is not newly claimed as formally
refined to the single-pool Lean model. Historical single-parent Lean modules remain
research artifacts and do not select runtime behavior.

Run from repository root:

```sh
python3 proofs/validator-budget/check_rust_multi_parent.py
cargo test -p cbcl-parser --test quorum_runtime
python3 proofs/validator-budget/check_rust_multi_parent_mutations.py
```

This is tested Rust correspondence, not universal source-code equivalence. The
finite catalogue, machine arithmetic and positive-amount/codec limits reject inputs
outside the supported projection. Cryptography, physical journal durability and
network decoding remain host assumptions. Neither unbounded fresh-ID refinement
nor complete/latest balance reads are proved. Current evidence:
[[unified-quorum-evidence]].

## Local execution cost

The runtime validates each event into a small owned update before atomic append,
then applies that update without repeating fallible protocol checks. Rejection,
failed append/CAS and validated retries leave in-memory state unchanged; signing
requests remain unavailable until persistence succeeds. No full-state clone is
needed to implement rollback.

Per-version charge totals are derived from signed/released journal evidence and
updated once on first sign/release. Adoption never resets them. Recovery rebuilds
the cache through the same validated transitions; serialized totals are not trusted.
Debug builds independently recompute the history sum after each applied update.
Read-only checks borrow stored manifests rather than cloning their held sets.

An ignored local probe measures four serial validators, a memory journal and test
authentication. It includes authoring, registration, operation QCs and effects
finality, but no network, real cryptography, fsync, version merges or adversarial
contention. Run with native speed optimization (the workspace release default is
size optimization):

```sh
CARGO_PROFILE_RELEASE_OPT_LEVEL=3 CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_DEBUG=0 \
  cargo test --release -p cbcl-parser --test quorum_runtime \
  multi_parent::in_memory_throughput_probe -- --ignored --exact --nocapture
```

There is no CI timing threshold. Measurements and validation are recorded in
[[quorum-local-cost-evidence]] under [[SPEC-032-quorum-local-update-cost]]. They do
not establish production TPS; networking, durable writes, real signatures and
history retention limits remain separate costs.
